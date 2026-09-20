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
  P.Body{o, 262144n, Nat.add(o, 786432n), P.Pos{102400n}, P.Pos{0n}, P.Pos{0n}, False{}, False{}, P.Rot.rest()}

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

# Um cubo equilibrado na quina de outro: o meio dele fica para fora do
# apoio, entao ele tem que escorregar da beirada e cair no chao. Antes
# ficava pendurado para sempre, porque qualquer encostada segurava.
# na pista, que o gerador deixa vazia, para nada mais entrar na conta:
# um cubo no chao e outro em cima dele com o meio para fora do apoio
def perched() -> W.World:
  +o = W.W.base(W.W.origin())
  W.World{12345, W.CGen{},
    [W.W.cube(Nat.add(o, 262144n), 0n, Nat.add(o, 2621440n)),
     W.W.cube(Nat.add(o, 466944n), 262144n, Nat.add(o, 2621440n))],
    [], W.W.cube(Nat.sub(o, 5242880n), 0n, o)}

def high(xs: List<&2, P.Body>, +m: Nat) -> Nat:
  match xs:
    case []:
      m
    case +b <> rest:
      high(rest, Nat.max(m, P.Body.y(b)))

# todos os cubos da regiao, acordados ou dormindo nas celulas
def todos(w: W.World) -> List<&2, P.Body>:
  W.World{+seed, +t, awake, dirty, p} = w
  List.append(&2, P.Body, awake,
    W.W.rect(48n, t, seed, (W.W.origin() - 2 : U32), (W.W.origin() + 8 : U32), 6n))

def tip(n: Nat, +bad: Nat, +w: W.World) -> String:
  match n:
    case 0n:
      M.Pick.s(Bool.and(Nat.is_eq(bad, 0n), Nat.is_eq(high(todos(w), 0n), 0n)), "OK", "FAIL")
        ++ ": " ++ Nat.show(bad) ++ " overlaps, o mais alto a "
        ++ M.Fmt.dec2(high(todos(w), 0n), 262144n) ++ " m (tem que acabar em 0,00: o cubo"
        ++ " empoleirado tem que tombar e cair)"
    case 1n+m:
      tip(m, Nat.add(bad, clash(todos(w))), W.W.tick_flat(M.Knob.defaults(), P.In.idle(), w))

# A rotacao tem que sobreviver ao array onde a multidao e guardada: um
# cubo girando que dorme, muda de chunk ou e empacotado tem que sair de la
# girando igual -- senao o giro some sem lei nenhuma pedir.
def spin() -> P.Rot:
  P.Rot{P.Quat{P.Pos{31000n}, P.Neg{5000n}, P.Pos{7000n}, P.Neg{3000n}},
    P.Wv{P.Pos{123456n}, P.Neg{4321n}, P.Pos{999n}}}

def spun() -> P.Body:
  +o = W.W.base(W.W.origin())
  P.Body{Nat.add(o, 262144n), 262144n, Nat.add(o, 2621440n), P.Pos{7n}, P.Pos{0n}, P.Neg{9n}, False{}, False{},
    spin()}

def og() -> W.Og:
  +o = W.W.base(W.W.origin())
  W.Og{o, o}

def zeq(+a: P.Z, +b: P.Z) -> Bool:
  Bool.and(Nat.is_eq(P.Z.pos(a), P.Z.pos(b)), Nat.is_eq(P.Z.neg(a), P.Z.neg(b)))

def qeq(+a: P.Quat, +b: P.Quat) -> Bool:
  Bool.and(Bool.and(zeq(P.Quat.a(a), P.Quat.a(b)), zeq(P.Quat.b(a), P.Quat.b(b))),
    Bool.and(zeq(P.Quat.c(a), P.Quat.c(b)), zeq(P.Quat.d(a), P.Quat.d(b))))

def weq(+a: P.Wv, +b: P.Wv) -> Bool:
  Bool.and(zeq(P.Wv.x(a), P.Wv.x(b)), Bool.and(zeq(P.Wv.y(a), P.Wv.y(b)), zeq(P.Wv.z(a), P.Wv.z(b))))

def same(+a: P.Rot, +b: P.Rot) -> Bool:
  Bool.and(qeq(P.Rot.q(a), P.Rot.q(b)), weq(P.Rot.w(a), P.Rot.w(b)))

def turn2(bs: List<&2, P.Body>) -> String:
  match bs:
    case []:
      "FAIL: o cubo sumiu do array"
    case +b <> rest:
      M.Pick.s(same(P.Body.rot(b), spin()), "OK", "FAIL") ++ ": quaternio "
        ++ Nat.show(P.Z.mag(P.Quat.a(P.Rot.q(P.Body.rot(b))))) ++ "/"
        ++ Nat.show(P.Z.mag(P.Quat.b(P.Rot.q(P.Body.rot(b))))) ++ ", giro "
        ++ Nat.show(P.Z.mag(P.Wv.x(P.Rot.w(P.Body.rot(b))))) ++ "/"
        ++ Nat.show(P.Z.mag(P.Wv.y(P.Rot.w(P.Body.rot(b))))) ++ " (31000/5000, 123456/4321)"

def turn1(r: Array<U32> & List<&2, P.Body>) -> String:
  (a, bs) = r
  turn2(bs)

def turn() -> String:
  turn1(W.F.unpack(1, W.F.pack([spun()], Array.new(U32, 8n, 0), 0, og(), False{}), 0, og()))

# Os quinze eixos contra a caixa reta: enquanto nada girou, o teste novo
# tem que dar exatamente o mesmo que o de sempre -- senao a rotacao muda
# o jogo dos cubos parados, que e quase todo o mundo.
def d(+i: Nat) -> Nat:
  Nat.add(700000n, Nat.mul(i, 43691n))

def boxy(+ax: Nat, +ay: Nat, +az: Nat, +bx: Nat, +by: Nat, +bz: Nat) -> Bool:
  Bool.and(P.Geo.ovl(262144n, ax, bx), Bool.and(P.Geo.ovl(262144n, az, bz), P.Geo.ovl(262144n, ay, by)))

def beq(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case False{} False{}:
      True{}
    case _ _:
      False{}

def one(+i: Nat, +j: Nat, +k: Nat) -> Nat:
  M.Pick.n(beq(boxy(1000000n, 1000000n, 1000000n, d(i), d(j), d(k)),
    P.Geo.sat(262144n, 1000000n, 1000000n, 1000000n, P.Quat.one(), d(i), d(j), d(k), P.Quat.one())), 0n, 1n)

def kk(+i: Nat, +j: Nat, k: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n++m:
      Nat.add(one(i, j, m), kk(i, j, m))

def jj(+i: Nat, j: Nat) -> Nat:
  match j:
    case 0n:
      0n
    case 1n++m:
      Nat.add(kk(i, m, 15n), jj(i, m))

def ii(i: Nat) -> Nat:
  match i:
    case 0n:
      0n
    case 1n++m:
      Nat.add(jj(m, 15n), ii(m))

def axes() -> String:
  M.Pick.s(Nat.is_eq(ii(15n), 0n), "OK", "FAIL") ++ ": " ++ Nat.show(ii(15n))
    ++ " diferencas em 3375 posicoes (tem que ser 0)"

def main() -> IO(Unit):
  do IO<Unit>:
    a : Unit <- IO.print("veloz x parede: " ++ run(40n, 0n, wld()))
    b : Unit <- IO.print("rotacao no array: " ++ turn())
    c : Unit <- IO.print("quinze eixos x caixa: " ++ axes())
    IO.print("quina:          " ++ tip(200n, 0n, perched()))
