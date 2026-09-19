# Cubo -- the game.
#
#   ./build.sh && ./cubo
#
# You are the blue cube. W A S D walk (the way the camera looks), Space
# jumps, the mouse turns the camera, the wheel brings it closer or
# further. Green cubes lie around, at random, forever in every direction:
# push them, climb on them. The physics' constants (gravity, the ground's
# friction, the jump, the motor) change while you play: Tab or the up and
# down arrows pick one, left and right change it, R puts them all back.
# Enter takes you back to the start, N makes a new world, H shows the
# keys, Esc quits.
#
# The world ticks 128 times a second (world.bend, phys.bend: every law of
# LAWS.bend holds for every tick, whatever the constants); frames come as
# fast as the GPU draws them (effs/scene.comp.in, through effs/screen.c),
# the player drawn between its last two ticks.

import Base
import ./phys.bend as P
import ./world.bend as W

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

def Pick.s(c: Bool, a: String, b: String) -> String:
  match c:
    case True{}:
      a
    case False{}:
      b

# The constants
# -------------
# phys.bend's K, six of them tunable: gravity (g/8 m/s^2), friction (mu
# in 256ths), the jump (m/s in 1024ths), the motor on the ground and in the
# air (m/s^2 in 8ths), the top walking speed (m/s in 1024ths). The size of
# a cube is fixed: a metre.

def Knob.count() -> Nat:
  6n

def Knob.defaults() -> P.K:
  P.K{78n, 179n, 5541n, 160n, 32n, 6144n, 262144n}

def Knob.get(k: P.K, i: Nat) -> Nat:
  P.K{g, mu, jump, acc, air, vmax, size} = k
  match i:
    case 0n:
      g
    case 1n:
      mu
    case 2n:
      jump
    case 3n:
      acc
    case 4n:
      air
    case _:
      vmax

def Knob.set(k: P.K, i: Nat, +v: Nat) -> P.K:
  P.K{g, mu, jump, acc, air, vmax, size} = k
  match i:
    case 0n:
      P.K{v, mu, jump, acc, air, vmax, size}
    case 1n:
      P.K{g, v, jump, acc, air, vmax, size}
    case 2n:
      P.K{g, mu, v, acc, air, vmax, size}
    case 3n:
      P.K{g, mu, jump, v, air, vmax, size}
    case 4n:
      P.K{g, mu, jump, acc, v, vmax, size}
    case _:
      P.K{g, mu, jump, acc, air, v, size}

# a step of knob i, and its top
def Knob.step(i: Nat) -> Nat:
  match i:
    case 0n:
      4n
    case 1n:
      13n
    case 2n:
      256n
    case 3n:
      8n
    case 4n:
      8n
    case _:
      512n

def Knob.most(i: Nat) -> Nat:
  match i:
    case 0n:
      400n
    case 1n:
      512n
    case 2n:
      U32.to_nat(20480)
    case 3n:
      U32.to_nat(1600)
    case 4n:
      800n
    case _:
      U32.to_nat(40960)

# knob i one step up (up) or down, within 0 .. most
def Knob.turn(+k: P.K, +i: Nat, up: Bool) -> P.K:
  +v = Knob.get(k, i)
  Knob.set(k, i, Pick.n(up, Nat.min(Nat.add(v, Knob.step(i)), Knob.most(i)), Nat.sub(v, Knob.step(i))))

# Text
# ----

def Fmt.pad2(+n: Nat) -> String:
  Pick.s(Nat.is_lt(n, 10n), "0" ++ Nat.show(n), Nat.show(n))

# num / den with two decimals (rounded), a comma between
def Fmt.dec2(+num: Nat, +den: Nat) -> String:
  +q = Nat.div(Nat.add(Nat.mul(num, 100n), Nat.div(den, 2n)), den)
  Nat.show(Nat.div(q, 100n)) ++ "," ++ Fmt.pad2(Nat.mod(q, 100n))

def Fmt.dec1(+num: Nat, +den: Nat) -> String:
  +q = Nat.div(Nat.add(Nat.mul(num, 10n), Nat.div(den, 2n)), den)
  Nat.show(Nat.div(q, 10n)) ++ "," ++ Nat.show(Nat.mod(q, 10n))

# how high a jump rises: jump^2 / g units, the energy's balance
def Fmt.rise(+k: P.K) -> String:
  P.K{+g, mu, +jump, acc, air, vmax, size} = k
  Pick.s(Nat.is_eq(g, 0n), "sem volta", Fmt.dec2(Nat.div(Nat.mul(jump, jump), Nat.max(g, 1n)), 262144n) ++ " m")

def Knob.line(+k: P.K, i: Nat) -> String:
  match i:
    case 0n:
      "Gravidade       " ++ Fmt.dec2(Knob.get(k, 0n), 8n) ++ " m/s²"
    case 1n:
      "Atrito do chão  µ " ++ Fmt.dec2(Knob.get(k, 1n), 256n)
    case 2n:
      "Pulo            " ++ Fmt.dec2(Knob.get(k, 2n), 1024n) ++ " m/s (sobe " ++ Fmt.rise(k) ++ ")"
    case 3n:
      "Força no chão   " ++ Fmt.dec2(Knob.get(k, 3n), 8n) ++ " m/s²"
    case 4n:
      "Força no ar     " ++ Fmt.dec2(Knob.get(k, 4n), 8n) ++ " m/s²"
    case _:
      "Vel. máxima     " ++ Fmt.dec2(Knob.get(k, 5n), 1024n) ++ " m/s"

# Angles
# ------
# A turn is 1024 steps; sin and cos in 4096ths (Bhaskara's rational
# approximation over a half turn, error under 0.2%).

def Ang.half(+q: U32) -> Nat:
  +u = U32.to_nat((q * (512 - q) : U32))
  Nat.div(Nat.mul(65536n, u), Nat.sub(U32.to_nat(1310720), Nat.mul(4n, u)))

def Ang.sin_at(low: Bool, +a: U32) -> P.Z:
  match low:
    case True{}:
      P.Pos{Ang.half(a)}
    case False{}:
      P.Neg{Ang.half((a - 512 : U32))}

def Ang.sin(+a: U32) -> P.Z:
  +b = (a .&. 1023 : U32)
  Ang.sin_at((b < 512 : U32), b)

def Ang.cos(+a: U32) -> P.Z:
  Ang.sin((a + 256 : U32))

def Z.neg(v: P.Z) -> P.Z:
  match v:
    case P.Pos{n}:
      P.Neg{n}
    case P.Neg{n}:
      P.Pos{n}

def Z.pick(c: Bool, a: P.Z, b: P.Z) -> P.Z:
  match c:
    case True{}:
      a
    case False{}:
      b

# the walk the keys ask for, from the camera's yaw: forward is (sin, cos),
# right is (-cos, sin); a diagonal shortened to keep the length 4096
def Walk.dir(+f: P.Z, +r: P.Z, +fwd: U32, +side: U32, +diag: Bool) -> P.Z:
  +a = Z.pick(U32.is_eq(fwd, 1), f, Z.pick(U32.is_eq(fwd, 2), Z.neg(f), P.Pos{0n}))
  +b = Z.pick(U32.is_eq(side, 1), r, Z.pick(U32.is_eq(side, 2), Z.neg(r), P.Pos{0n}))
  +s = P.Z.add(a, b)
  Z.pick(diag, P.Z.q12(2896n, s), s)

def Walk.some(none: Bool, ux: P.Z, uz: P.Z) -> Maybe<&2, P.Wish>:
  match none:
    case True{}:
      None{}
    case False{}:
      Some{P.Wish{ux, uz}}

# Input
# -----
# A frame's events fold into the held keys, the mouse and the discrete
# actions. Esc or closing the window quits.

type Act is Data:
  Sel{up: Bool}
  Adj{up: Bool}
  Reset{}
  Help{}
  Home{}
  Fresh{}
  Zoom{out: Bool}
  Stats{gpu: U32, all: U32}
  Choose{i: U32}

type Inp is Data:
  Inp{keys: U32, mx: U32, my: U32, seen: Bool, dx: U32, dy: U32, acts: List<&2, Act>}

# the held-key bit of a key: W S A D Space, then left and right

def Walk.wish(+keys: U32, +yaw: U32) -> Maybe<&2, P.Wish>:
  +w = U32.is_eq((keys .&. 1 : U32), 1)
  +s = U32.is_eq((keys .&. 2 : U32), 2)
  +a = U32.is_eq((keys .&. 4 : U32), 4)
  +d = U32.is_eq((keys .&. 8 : U32), 8)
  +fwd = Pick.u(Bool.and(w, Bool.not(s)), 1, Pick.u(Bool.and(s, Bool.not(w)), 2, 0))
  +side = Pick.u(Bool.and(d, Bool.not(a)), 1, Pick.u(Bool.and(a, Bool.not(d)), 2, 0))
  +diag = Bool.and(Bool.not(U32.is_eq(fwd, 0)), Bool.not(U32.is_eq(side, 0)))
  +sn = Ang.sin(yaw)
  +cs = Ang.cos(yaw)
  Walk.some(Bool.and(U32.is_eq(fwd, 0), U32.is_eq(side, 0)),
    Walk.dir(sn, Z.neg(cs), fwd, side, diag), Walk.dir(cs, sn, fwd, side, diag))

def Inp.bit(+code: U32) -> U32:
  Pick.u(U32.is_eq(code, 119), 1, Pick.u(U32.is_eq(code, 115), 2, Pick.u(U32.is_eq(code, 97), 4,
    Pick.u(U32.is_eq(code, 100), 8, Pick.u(U32.is_eq(code, 32), 16,
    Pick.u(U32.is_eq(code, 63234), 32, Pick.u(U32.is_eq(code, 63235), 64, 0)))))))

def Inp.digit(ok: Bool, +code: U32) -> Maybe<&2, Act>:
  match ok:
    case True{}:
      Some{Choose{(code - 49 : U32)}}
    case False{}:
      None{}

def Inp.act_more(r: Bool, h: Bool, enter: Bool, n: Bool, wup: Bool, wdown: Bool, +code: U32) -> Maybe<&2, Act>:
  match r h enter n wup wdown:
    case True{} _ _ _ _ _:
      Some{Reset{}}
    case False{} True{} _ _ _ _:
      Some{Help{}}
    case False{} False{} True{} _ _ _:
      Some{Home{}}
    case False{} False{} False{} True{} _ _:
      Some{Fresh{}}
    case False{} False{} False{} False{} True{} _:
      Some{Zoom{False{}}}
    case False{} False{} False{} False{} False{} True{}:
      Some{Zoom{True{}}}
    case False{} False{} False{} False{} False{} False{}:
      Inp.digit(Bool.and((code >= 49 : U32), (code <= 54 : U32)), code)

def Inp.act_at(tab: Bool, upk: Bool, down: Bool, left: Bool, right: Bool, +code: U32) -> Maybe<&2, Act>:
  match tab upk down left right:
    case True{} _ _ _ _:
      Some{Sel{False{}}}
    case False{} True{} _ _ _:
      Some{Sel{True{}}}
    case False{} False{} True{} _ _:
      Some{Sel{False{}}}
    case False{} False{} False{} True{} _:
      Some{Adj{False{}}}
    case False{} False{} False{} False{} True{}:
      Some{Adj{True{}}}
    case False{} False{} False{} False{} False{}:
      Inp.act_more(U32.is_eq(code, 114), U32.is_eq(code, 104), U32.is_eq(code, 13), U32.is_eq(code, 110),
        U32.is_eq(code, 63300), U32.is_eq(code, 63301), code)

def Inp.act_of(+code: U32) -> Maybe<&2, Act>:
  Inp.act_at(U32.is_eq(code, 9), U32.is_eq(code, 63232), U32.is_eq(code, 63233), U32.is_eq(code, 63234),
    U32.is_eq(code, 63235), code)

def Inp.push(m: Maybe<&2, Act>, acts: List<&2, Act>) -> List<&2, Act>:
  match m:
    case None{}:
      acts
    case Some{a}:
      a <> acts

def Pick.m(c: Bool, m: Maybe<&2, Act>) -> Maybe<&2, Act>:
  match c:
    case True{}:
      m
    case False{}:
      None{}

def Inp.press(+code: U32, +down: Bool, s: Inp) -> Inp:
  Inp{+keys, mx, my, seen, dx, dy, acts} = s
  +bit = Inp.bit(code)
  Inp{Pick.u(down, (keys .|. bit : U32), (keys .&. U32.not(bit) : U32)), mx, my, seen, dx, dy,
    Inp.push(Pick.m(down, Inp.act_of(code)), acts)}

def Inp.key(quit: Bool, +code: U32, +down: Bool, s: Inp) -> Maybe<&2, Inp>:
  match quit:
    case True{}:
      None{}
    case False{}:
      Some{Inp.press(code, down, s)}

def Inp.look_at(seen: Bool, +x: U32, +y: U32, +keys: U32, +mx: U32, +my: U32, +dx: U32, +dy: U32, acts: List<&2, Act>) -> Inp:
  match seen:
    case True{}:
      Inp{keys, x, y, True{}, (dx + x - mx : U32), (dy + y - my : U32), acts}
    case False{}:
      Inp{keys, x, y, True{}, dx, dy, acts}

# the mouse moved to (x, y): the motion adds up, a step a pixel
def Inp.look(+x: U32, +y: U32, s: Inp) -> Inp:
  Inp{keys, +mx, +my, seen, +dx, +dy, acts} = s
  Inp.look_at(seen, x, y, keys, mx, my, dx, dy, acts)

def Inp.stats(ok: Bool, +x: U32, +y: U32, s: Inp) -> Inp:
  match ok:
    case True{}:
      Inp{keys, mx, my, seen, dx, dy, acts} = s
      Inp{keys, mx, my, seen, dx, dy, Stats{x, y} <> acts}
    case False{}:
      s

def Inp.mouse(+button: U32, +x: U32, +y: U32, s: Inp) -> Inp:
  Inp.stats(U32.is_eq(button, 100), x, y, s)

def Inp.event(e: Event, s: Inp) -> Maybe<&2, Inp>:
  match e:
    case Key{+code, +down}:
      Inp.key(Bool.and(U32.is_eq(code, 27), down), code, down, s)
    case Mouse{+x, +y, +button, down}:
      Some{Inp.mouse(button, x, y, s)}
    case Move{x, y}:
      Some{Inp.look(x, y, s)}
    case Close{}:
      None{}

def Inp.events(evs: List<Event>, s: Inp) -> Maybe<&2, Inp>:
  match evs:
    case []:
      Some{s}
    case e <> rest:
      Maybe.bind(&2, Inp, Inp, Inp.event(e, s), s2 => Inp.events(rest, s2))

# Text
# ----
# A line of the HUD: its characters (Latin-1) four to a word.

def Txt.emit(full: Bool, +w: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match full:
    case True{}:
      w <> rest
    case False{}:
      rest

def Pick.l(c: Bool, a: List<&2, U32>, b: List<&2, U32>) -> List<&2, U32>:
  match c:
    case True{}:
      a
    case False{}:
      b

def Txt.pack(s: String, +k: U32, +acc: U32) -> List<&2, U32>:
  match s:
    case SNil{}:
      Pick.l(U32.is_eq(k, 0), [], [acc])
    case SCon{Chr{c}, rest}:
      +w = (acc .|. ((c .&. 255) << U32.to_nat((k * 8 : U32))) : U32)
      +full = U32.is_eq(k, 3)
      Txt.emit(full, w, Txt.pack(rest, Pick.u(full, 0, (k + 1 : U32)), Pick.u(full, 0, w)))

# The frame
# ---------
# The header effs/screen.c hands the GPU (effs/scene.comp.in reads it):
# the seed, the cell the view is centred on, the player (drawn between
# its last two ticks), the camera, the moving bodies, the HUD's lines;
# from word 2048 the changed cells (world.bend's dirty ones).

type Put is Data:
  Put{i: U32, v: U32}

def Buf.write(ws: List<&2, Put>, a: Array<U32>) -> Array<U32>:
  match ws:
    case []:
      a
    case Put{i, v} <> rest:
      Buf.write(rest, Array.set(U32, a, i, v))

# a line's words at word base, the rest of its 24 cleared
def Txt.puts(n: Nat, ws: List<&2, U32>, +base: U32) -> List<&2, Put>:
  match n ws:
    case 0n _:
      []
    case 1n+m Nil{}:
      Put{base, 0} <> Txt.puts(m, [], (base + 1 : U32))
    case 1n+m +w <> rest:
      Put{base, w} <> Txt.puts(m, rest, (base + 1 : U32))

def Txt.line(+i: U32, s: String) -> List<&2, Put>:
  Txt.puts(24n, Txt.pack(s, 0, 0), (1056 + i * 24 : U32))

def Txt.lines(ls: List<&2, String>, +i: U32) -> List<&2, Put>:
  match ls:
    case []:
      []
    case s <> rest:
      List.append(&2, Put, Txt.line(i, s), Txt.lines(rest, (i + 1 : U32)))

# a position relative to the view's cell, wrapping in 32 bits
def Frame.rel(+x: Nat, +c: U32) -> U32:
  (U32.from_nat(x) - U32.from_nat(W.W.base(c)) : U32)

def Frame.dyn(bs: List<&2, P.Body>, +j: U32, +ocx: U32, +ocz: U32) -> List<&2, Put>:
  match bs:
    case []:
      []
    case +b <> rest:
      +o = (32 + j * 4 : U32)
      Put{o, Frame.rel(P.Body.x(b), ocx)} <> Put{(o + 1 : U32), U32.from_nat(P.Body.y(b))}
        <> Put{(o + 2 : U32), Frame.rel(P.Body.z(b), ocz)} <> Put{(o + 3 : U32), Pick.u(U32.is_eq(j, 0), 1, 0)}
        <> Frame.dyn(rest, (j + 1 : U32), ocx, ocz)

# a cell's cubes, four words each: where in the cell, x y z
def Frame.cubes(bs: List<&2, P.Body>, +o: U32, +cx: U32, +cz: U32) -> List<&2, Put>:
  match bs:
    case []:
      []
    case +b <> rest:
      Put{o, U32.from_nat(Nat.sub(P.Body.x(b), W.W.base(cx)))} <> Put{(o + 1 : U32), U32.from_nat(P.Body.y(b))}
        <> Put{(o + 2 : U32), U32.from_nat(Nat.sub(P.Body.z(b), W.W.base(cz)))} <> Frame.cubes(rest, (o + 4 : U32), cx, cz)

def Frame.patch(+t: W.Cells, +seed: U32, +cx: U32, +cz: U32, +o: U32) -> List<&2, Put>:
  +cubes = W.Cells.at(t, seed, cx, cz)
  Put{o, cx} <> Put{(o + 1 : U32), cz} <> Put{(o + 2 : U32), U32.from_nat(Nat.min(List.length(&2, P.Body, cubes), 7n))}
    <> Frame.cubes(cubes, (o + 4 : U32), cx, cz)

type Patches is Data:
  Patches{puts: List<&2, Put>, n: U32, rest: List<&2, W.Cell>}

def Frame.more(p: Patches, +put: List<&2, Put>) -> Patches:
  Patches{puts, n, rest} = p
  Patches{List.append(&2, Put, put, puts), (n + 1 : U32), rest}

type Play is Data:
  Play{w: W.World, k: P.K, inp: Inp, t0: Nat, ticks: Nat, rep: Nat, prev: P.Body, yaw: U32, pitch: U32, dist: U32,
    sel: Nat, help: Bool, gpu: U32, fus: U32, hud: Bool}

# up to 180 of the changed cells (ok: this one fits): their patches, how
# many, and the ones left for the next frame
def Frame.patches(cells: List<&2, W.Cell>, +t: W.Cells, +seed: U32, +i: U32, ok: Bool) -> Patches:
  match cells ok:
    case Nil{} _:
      Patches{[], 0, []}
    case +c <> +rest False{}:
      Patches{[], 0, c <> rest}
    case W.Cell{+cx, +cz} <> +rest True{}:
      Frame.more(Frame.patches(rest, t, seed, (i + 1 : U32), ((i + 1 : U32) < 180 : U32)),
        Frame.patch(t, seed, cx, cz, (2049 + i * 32 : U32)))

# Play
# ----
# The world, the constants, the input, the clocks (t0 the start, ticks
# the physics ticks run, rep the next repeat of a held left/right), the
# player one tick back (prev, to draw between), the camera (yaw, pitch in
# 1024ths of a turn, distance in units), the knob picked, the help shown,
# the timings effs/screen.c reports.

# the player's input for a tick: the walk the keys ask for, the jump held
def Play.input(+keys: U32, +yaw: U32) -> P.In:
  P.In{Walk.wish(keys, yaw), U32.is_eq((keys .&. 16 : U32), 16)}

def Play.pl(w: W.World) -> P.Body:
  W.World{seed, t, awake, dirty, p} = w
  p

# n ticks of the world with the input held, and the player before the last
def Play.walks(n: Nat, +k: P.K, +inp: P.In, +prev: P.Body, +w: W.World) -> W.World & P.Body:
  match n:
    case 0n:
      (w, prev)
    case 1n+m:
      Play.walks(m, k, inp, Play.pl(w), W.W.tick(k, inp, w))

# k/1000 of the way from a to b
def Play.lerp(+a: Nat, +b: Nat, +k: Nat) -> Nat:
  Pick.n(Nat.is_le(a, b), Nat.add(a, Nat.div(Nat.mul(Nat.sub(b, a), k), 1000n)),
    Nat.sub(a, Nat.div(Nat.mul(Nat.sub(a, b), k), 1000n)))

def Play.between(+a: P.Body, +b: P.Body, +k: Nat) -> P.Body:
  W.W.cube(Play.lerp(P.Body.x(a), P.Body.x(b), k), Play.lerp(P.Body.y(a), P.Body.y(b), k),
    Play.lerp(P.Body.z(a), P.Body.z(b), k))

# a body's speed in 1024ths of m/s
def Play.speed(+b: P.Body) -> Nat:
  +x = P.Z.mag(P.Body.vx(b))
  +y = P.Z.mag(P.Body.vy(b))
  +z = P.Z.mag(P.Body.vz(b))
  P.Fric.floor(Nat.add(Nat.add(Nat.mul(x, x), Nat.mul(y, y)), Nat.mul(z, z)), Nat.add(Nat.add(x, y), z))

def Play.knobs(+k: P.K, +sel: Nat, +i: Nat) -> List<&2, String>:
  match i:
    case 0n:
      []
    case 1n+j:
      List.append(&2, String, Play.knobs(k, sel, j), [Pick.s(Nat.is_eq(j, sel), "» ", "  ") ++ Knob.line(k, j)])

def Play.helps(help: Bool) -> List<&2, String>:
  match help:
    case True{}:
      ["", "W A S D anda (para onde a câmera olha) · Espaço pula",
        "mouse gira a câmera · roda aproxima e afasta",
        "Enter volta ao início · N mundo novo · Esc sai",
        "empurre os cubos verdes · suba neles pulando",
        "12 leis provadas (LAWS.bend): energia no voo, cinemática,",
        "Coulomb, trabalho do atrito, momento no choque, sem atravessar"]
    case False{}:
      []

def Play.awake_of(w: W.World) -> List<&2, P.Body>:
  W.World{seed, t, awake, dirty, p} = w
  awake

def List.cat(a: List<&2, String>, b: List<&2, String>) -> List<&2, String>:
  List.append(&2, String, a, b)

# the HUD's lines
# the HUD's first two lines: the frame rate and the GPU's time, the
# player's height, speed and energy (they change every frame)
def Play.hud_top(+s: Play) -> List<&2, String>:
  Play{+w, +k, inp, t0, ticks, rep, prev, yaw, pitch, dist, sel, help, +gpu, +fus, hv} = s
  +p = Play.pl(w)
  ["CUBO AZUL  ·  " ++ Nat.show(Nat.div(1000000n, Nat.max(U32.to_nat(fus), 1n))) ++ " fps  ·  GPU "
     ++ Fmt.dec2(U32.to_nat(gpu), 1000n) ++ " ms",
   "altura " ++ Fmt.dec2(P.Body.y(p), 262144n) ++ " m   vel " ++ Fmt.dec2(Play.speed(p), 1024n) ++ " m/s   energia "
     ++ Fmt.dec1(P.Body.energy(P.K.g(k), p), U32.to_nat(2097152)) ++ " J/kg   cubos em movimento "
     ++ Nat.show(List.length(&2, P.Body, Play.awake_of(w)))]

# the rest (the constants, the keys): they change with the actions
def Play.hud_rest(+s: Play) -> List<&2, String>:
  Play{w, +k, inp, t0, ticks, rep, prev, yaw, pitch, dist, +sel, help, gpu, fus, hv} = s
  "" <> List.append(&2, String, Play.knobs(k, sel, Knob.count()),
    List.cat(["Tab/setas escolhem e mudam · R volta ao padrão · H ajuda"], Play.helps(help)))

def Play.hud(+s: Play) -> List<&2, String>:
  List.append(&2, String, Play.hud_top(s), Play.hud_rest(s))

# the lines to write: the top two, and the rest when they changed
def Play.hud_puts(hud: Bool, +s: Play) -> List<&2, Put>:
  match hud:
    case True{}:
      Txt.lines(Play.hud(s), 0)
    case False{}:
      Txt.lines(Play.hud_top(s), 0)

def Play.hud_count(+s: Play) -> U32:
  U32.from_nat(Nat.add(2n, List.length(&2, String, Play.hud_rest(s))))

# the frame's header: written into hdr; the world's dirty cells taken
def Play.head(+s: Play, +now: Nat, +pts: Patches, hdr: Array<U32>) -> Array<U32>:
  Play{+w, k, inp, +t0, ticks, rep, +prev, +yaw, +pitch, +dist, +sel, help, gpu, fus, +hv} = s
  W.World{+seed, t, +awake, dirty, +p} = w
  Patches{+puts, +n, rest} = pts
  +sub = Nat.mod(Nat.mul(Nat.sub(now, t0), 128n), 1000n)
  +eye = Play.between(prev, p, sub)
  +ocx = W.W.cell_of(P.Body.x(eye))
  +ocz = W.W.cell_of(P.Body.z(eye))
  Buf.write(List.append(&2, Put,
    [Put{0, seed}, Put{1, ocx}, Put{2, ocz}, Put{3, Frame.rel(P.Body.x(eye), ocx)}, Put{4, U32.from_nat(P.Body.y(eye))},
     Put{5, Frame.rel(P.Body.z(eye), ocz)}, Put{6, yaw}, Put{7, pitch}, Put{8, dist}, Put{9, U32.from_nat(now)},
     Put{10, U32.from_nat(Nat.min(Nat.add(List.length(&2, P.Body, awake), 1n), 250n))},
     Put{11, Play.hud_count(s)}, Put{12, U32.from_nat(Nat.add(sel, 3n))}, Put{13, 1},
     Put{2048, n}],
    List.append(&2, Put, Frame.dyn(eye <> awake, 0, ocx, ocz), List.append(&2, Put, Play.hud_puts(hv, s), puts))), hdr)

def Play.untake(s: Play, rest: List<&2, W.Cell>) -> Play:
  Play{w, k, inp, t0, ticks, rep, prev, yaw, pitch, dist, sel, help, gpu, fus, hv} = s
  W.World{seed, t, awake, dirty, p} = w
  Play{W.World{seed, t, awake, rest, p}, k, inp, t0, ticks, rep, prev, yaw, pitch, dist, sel, help, gpu, fus, False{}}

def Play.view2(+s: Play, +now: Nat, +pts: Patches, hdr: Array<U32>) -> Play & Array<U32>:
  Patches{puts, n, +rest} = pts
  (Play.untake(s, rest), Play.head(s, now, pts, hdr))

def Play.view(+s: Play, +now: Nat, hdr: Array<U32>) -> Play & Array<U32>:
  Play{+w, k, inp, t0, ticks, rep, prev, yaw, pitch, dist, sel, help, gpu, fus, hv} = s
  W.World{+seed, +t, awake, +dirty, p} = w
  Play.view2(s, now, Frame.patches(dirty, t, seed, 0, True{}), hdr)

# The tick
# --------

def Play.sel(up: Bool, s: Play) -> Play:
  Play{w, k, inp, t0, ticks, rep, prev, yaw, pitch, dist, +sel, help, gpu, fus, hv} = s
  Play{w, k, inp, t0, ticks, rep, prev, yaw, pitch, dist, Nat.mod(Nat.add(sel, Pick.n(up, 5n, 1n)), Knob.count()), help, gpu, fus, True{}}

def Play.adj(+up: Bool, +now: Nat, s: Play) -> Play:
  Play{w, +k, inp, t0, ticks, rep, prev, yaw, pitch, dist, +sel, help, gpu, fus, hv} = s
  Play{w, Knob.turn(k, sel, up), inp, t0, ticks, Nat.add(now, 300n), prev, yaw, pitch, dist, sel, help, gpu, fus, True{}}

def Play.reset(s: Play) -> Play:
  Play{w, k, inp, t0, ticks, rep, prev, yaw, pitch, dist, sel, help, gpu, fus, hv} = s
  Play{w, Knob.defaults(), inp, t0, ticks, rep, prev, yaw, pitch, dist, sel, help, gpu, fus, True{}}

def Play.help(s: Play) -> Play:
  Play{w, k, inp, t0, ticks, rep, prev, yaw, pitch, dist, sel, help, gpu, fus, hv} = s
  Play{w, k, inp, t0, ticks, rep, prev, yaw, pitch, dist, sel, Bool.not(help), gpu, fus, True{}}

def Play.home(s: Play) -> Play:
  Play{w, k, inp, t0, ticks, rep, prev, yaw, pitch, dist, sel, help, gpu, fus, hv} = s
  W.World{+seed, t, awake, dirty, p} = w
  Play{W.World{seed, t, awake, dirty, Play.pl(W.W.new(seed))}, k, inp, t0, ticks, rep,
    Play.pl(W.W.new(seed)), yaw, pitch, dist, sel, help, gpu, fus, hv}

def Play.fresh(+now: Nat, s: Play) -> Play:
  Play{w, k, inp, t0, ticks, rep, prev, yaw, pitch, dist, sel, help, gpu, fus, hv} = s
  W.World{+seed, t, awake, dirty, p} = w
  +seed2 = W.Hash.mix((seed + U32.from_nat(now) + 1 : U32))
  Play{W.W.new(seed2), k, inp, t0, ticks, rep, Play.pl(W.W.new(seed2)), yaw, pitch, dist, sel, help, gpu, fus, hv}

def Play.zoom(out: Bool, s: Play) -> Play:
  Play{w, k, inp, t0, ticks, rep, prev, yaw, pitch, +dist, sel, help, gpu, fus, hv} = s
  Play{w, k, inp, t0, ticks, rep, prev, yaw, pitch,
    U32.min(U32.max(Pick.u(out, (dist + 196608 : U32), (dist - 196608 : U32)), 393216), 6553600), sel, help, gpu, fus, hv}

def Play.stats(+g2: U32, +all: U32, s: Play) -> Play:
  Play{w, k, inp, t0, ticks, rep, prev, yaw, pitch, dist, sel, help, gpu, fus, hv} = s
  Play{w, k, inp, t0, ticks, rep, prev, yaw, pitch, dist, sel, help, g2, all, hv}

def Play.choose(+i: U32, s: Play) -> Play:
  Play{w, k, inp, t0, ticks, rep, prev, yaw, pitch, dist, sel, help, gpu, fus, hv} = s
  Play{w, k, inp, t0, ticks, rep, prev, yaw, pitch, dist, Nat.min(U32.to_nat(i), 5n), help, gpu, fus, True{}}

def Play.act(a: Act, +now: Nat, s: Play) -> Play:
  match a:
    case Sel{up}:
      Play.sel(up, s)
    case Adj{up}:
      Play.adj(up, now, s)
    case Reset{}:
      Play.reset(s)
    case Help{}:
      Play.help(s)
    case Home{}:
      Play.home(s)
    case Fresh{}:
      Play.fresh(now, s)
    case Zoom{out}:
      Play.zoom(out, s)
    case Stats{g2, all}:
      Play.stats(g2, all, s)
    case Choose{i}:
      Play.choose(i, s)

def Play.acts(xs: List<&2, Act>, +now: Nat, s: Play) -> Play:
  match xs:
    case []:
      s
    case a <> rest:
      Play.acts(rest, now, Play.act(a, now, s))

# a held left or right: after 300 ms, a step every 60 ms
def Play.repeat(on: Bool, +right: Bool, +now: Nat, s: Play) -> Play:
  match on:
    case True{}:
      Play{w, +k, inp, t0, ticks, rep, prev, yaw, pitch, dist, +sel, help, gpu, fus, hv} = s
      Play{w, Knob.turn(k, sel, right), inp, t0, ticks, Nat.add(now, 60n), prev, yaw, pitch, dist, sel, help, gpu, fus, True{}}
    case False{}:
      s

def Play.held(+keys: U32, +now: Nat, +s: Play) -> Play:
  Play{w, k, inp, t0, ticks, +rep, prev, yaw, pitch, dist, sel, help, gpu, fus, hv} = s
  +lr = (keys .&. 96 : U32)
  Play.repeat(Bool.and(Bool.and(Bool.not(U32.is_eq(lr, 0)), Bool.not(U32.is_eq(lr, 96))),
    Bool.and(Nat.is_lt(0n, rep), Nat.is_le(rep, now))), U32.is_eq(lr, 64), now, s)

# the mouse's motion turns the camera: a step a pixel; the pitch kept
# between a little up and nearly straight down
def Play.look(+dx: U32, +dy: U32, s: Play) -> Play:
  Play{w, k, inp, t0, ticks, rep, prev, +yaw, +pitch, dist, sel, help, gpu, fus, hv} = s
  Play{w, k, inp, t0, ticks, rep, prev, ((yaw - dx) .&. 1023 : U32),
    (U32.min(U32.max((pitch + 4096 + dy : U32), 4292), 4582) - 4096 : U32), dist, sel, help, gpu, fus, hv}

def Play.ran(r: W.World & P.Body, +k: P.K, inp: Inp, +t0: Nat, +ticks: Nat, +rep: Nat, +yaw: U32, +pitch: U32, +dist: U32,
  +sel: Nat, help: Bool, +gpu: U32, +fus: U32, hud: Bool) -> Play:
  (w, prev) = r
  Play{w, k, inp, t0, ticks, rep, prev, yaw, pitch, dist, sel, help, gpu, fus, hud}

# the physics' ticks due by now (128 a second), at most 8 a frame
def Play.physics(+keys: U32, +now: Nat, s: Play) -> Play:
  Play{w, +k, inp, +t0, +ticks, rep, +prev, +yaw, pitch, dist, sel, help, gpu, fus, hv} = s
  +due = Nat.div(Nat.mul(Nat.sub(now, t0), 128n), 1000n)
  +behind = Nat.sub(due, ticks)
  Play.ran(Play.walks(Nat.min(behind, 8n), k, Play.input(keys, yaw), prev, w), k, inp, t0,
    Pick.n(Nat.is_lt(8n, behind), due, Nat.add(ticks, Nat.min(behind, 8n))), rep, yaw, pitch, dist, sel, help, gpu, fus, hv)

def Play.with_inp(s: Play, inp: Inp) -> Play:
  Play{w, k, old, t0, ticks, rep, prev, yaw, pitch, dist, sel, help, gpu, fus, hv} = s
  Play{w, k, inp, t0, ticks, rep, prev, yaw, pitch, dist, sel, help, gpu, fus, hv}

def Play.go(+now: Nat, m: Maybe<&2, Inp>, s: Play) -> Maybe<&2, Play>:
  match m:
    case None{}:
      None{}
    case Some{inp}:
      Inp{+keys, mx, my, seen, +dx, +dy, acts} = inp
      Some{Play.physics(keys, now, Play.held(keys, now, Play.acts(List.reverse(&2, Act, acts), now,
        Play.look(dx, dy, Play.with_inp(s, Inp{keys, mx, my, seen, 0, 0, []})))))}

def Play.inp(s: Play) -> Inp:
  Play{w, k, inp, t0, ticks, rep, prev, yaw, pitch, dist, sel, help, gpu, fus, hv} = s
  inp

# the demo's input (./cubo demo): W held, a jump every 1.5 s, the camera
# turning slowly
def Play.demo(demo: Bool, +now: Nat, +t0: Nat, events: List<Event>) -> List<Event>:
  match demo:
    case True{}:
      +t = Nat.sub(now, t0)
      Key{119, True{}} <> Key{32, Nat.is_lt(Nat.mod(t, 1500n), 150n)}
        <> Move{U32.from_nat(Nat.div(t, 25n)), 0} <> events
    case False{}:
      events

def Play.t0(s: Play) -> Nat:
  Play{w, k, inp, t0, ticks, rep, prev, yaw, pitch, dist, sel, help, gpu, fus, hv} = s
  t0

def Play.tock(+now: Nat, events: List<Event>, +s: Play, demo: Bool) -> Maybe<&2, Play>:
  Play.go(now, Inp.events(Play.demo(demo, now, Play.t0(s), events), Play.inp(s)), s)

def Play.tick(events: List<Event>, +s: Play, demo: Bool) -> IO(Maybe<&2, Play>):
  do IO<Maybe<&2, Play>>:
    now : Nat <- IO.now()
    return Play.tock(now, events, s, demo)

def Play.start_at(+now: Nat, +seed: U32) -> Play:
  +w = W.W.new(seed)
  Play{w, Knob.defaults(), Inp{0, 0, 0, False{}, 0, 0, []}, now, 0n, 0n, Play.pl(w), 0, 330, 1572864, 0n,
    True{}, 0, 16666, True{}}

# The loop
# --------
# Base's App loop, reshaped for the GPU: a frame writes the header
# (Play.view), effs/screen.c draws it and hands back the events, which
# tick the game.

# a new game at now: a world of a seed from the clock
def Play.start(+now: Nat) -> Play:
  Play.start_at(now, W.Hash.mix((U32.from_nat(now) * 2654435769 : U32)))

def Screen.show(window: Window, hdr: Array<U32>) -> IO(Window & Array<U32> & List<Event>):
  import "./effs/screen.c"
  import "./effs/screen.js"

def Loop.next(window: Window, hdr: Array<U32>, rest: Window -> Array<U32> -> Play -> IO(Unit), m: Maybe<&2, Play>)
  -> IO(Unit):
  match m:
    case None{}:
      Window.close(window)
    case Some{s}:
      rest(window, hdr, s)

def Loop.turn(shown: Window & Array<U32> & List<Event>, +s: Play, demo: Bool, rest: Window -> Array<U32> -> Play -> IO(Unit))
  -> IO(Unit):
  (window, hdr, events) = shown
  IO.bind(Maybe<&2, Play>, Unit, Play.tick(events, s, demo), m => Loop.next(window, hdr, rest, m))

def Loop.frame(v: Play & Array<U32>, window: Window, demo: Bool, rest: Window -> Array<U32> -> Play -> IO(Unit)) -> IO(Unit):
  (+s, hdr) = v
  do IO<Unit>:
    shown : Window & Array<U32> & List<Event> <- Screen.show(window, hdr)
    Loop.turn(shown, s, demo, rest)

def Loop.go(fuel: Nat, window: Window, hdr: Array<U32>, +s: Play, +demo: Bool) -> IO(Unit):
  match fuel:
    case 0n:
      Window.close(window)
    case 1n+f:
      do IO<Unit>:
        now : Nat <- IO.now()
        Loop.frame(Play.view(s, now, hdr), window, demo, w => h => s2 => Loop.go(f, w, h, s2, demo))

type Flags is Data:
  Flags{still: Bool, demo: Bool}

def Args.flag(+a: String, f: Flags) -> Flags:
  Flags{still, demo} = f
  Flags{Bool.or(still, String.eq(a, "still")), Bool.or(demo, String.eq(a, "demo"))}

def Args.flags(args: List<String>) -> Flags:
  match args:
    case []:
      Flags{False{}, False{}}
    case +a <> rest:
      Args.flag(a, Args.flags(rest))

# ./cubo still: the world of seed 12345, nothing moving (to measure)
def Play.first(still: Bool, +now: Nat) -> Play:
  match still:
    case True{}:
      Play.start_at(now, 12345)
    case False{}:
      Play.start(now)

def Main.go(+now: Nat, window: Window, f: Flags) -> IO(Unit):
  Flags{still, +demo} = f
  Loop.go(U32.to_nat(4294967295), window, Array.new(U32, 13n, 0), Play.first(still, now), demo)

def main() -> IO(Unit):
  do IO<Unit>:
    now : Nat <- IO.now()
    args : List<String> <- IO.args
    window : Window <- IO.try(Window, Window.open("Cubo", 1280, 720))
    Main.go(now, window, Args.flags(args))
