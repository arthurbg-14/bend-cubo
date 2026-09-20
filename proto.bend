# prototipo: N chunks persistentes, cada um no seu array, ticando em paralelo
import Base
import ./phys.bend as P
import ./world.bend as W
import ./main.bend as M

def k0() -> P.K:
  M.Knob.defaults()

# um corpo do chunk (bx, bz), na posicao i dentro dele: uma grade de cubos
# espacados 1,15 m, caindo
def body(+o2: Nat, +bx: Nat, +bz: Nat, +i: Nat, +side: Nat) -> P.Body:
  +o = W.W.base(W.W.origin())
  P.Body{Nat.add(o, Nat.add(Nat.mul(Nat.add(Nat.mul(bx, 16n), Nat.mod(i, 14n)), 294912n), 16384n)),
    Nat.mul(Nat.add(Nat.div(i, 196n), 4n), 294912n),
    Nat.add(o, Nat.add(Nat.mul(Nat.add(Nat.mul(bz, 16n), Nat.mod(Nat.div(i, 14n), 14n)), 294912n), 16384n)),
    P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, False{}, False{}}

def rows(+n: Nat, +o: Nat, +bx: Nat, +bz: Nat, +side: Nat) -> List<&2, P.Body>:
  match n:
    case 0n:
      []
    case 1n+m:
      body(o, bx, bz, m, side) <> rows(m, o, bx, bz, side)

# o array de um chunk: os corpos empacotados e a grade montada
def chunk(+n: Nat, +bx: Nat, +bz: Nat, +side: Nat, r: U32 & Nat) -> W.Fa:
  (+cap, b) = r
  W.FaL{W.F.build(U32.from_nat(n), W.F.pack(rows(n, W.W.base(W.W.origin()), bx, bz, side),
    Array.new(U32, Nat.add(b, 4n), 0), 0, W.Og{W.W.base(W.W.origin()), W.W.base(W.W.origin())}, False{}),
    cap, (cap - 1 : U32)), U32.from_nat(n), U32.from_nat(n), cap}

# uma arvore de 2^d chunks
def tree(d: Nat, +i: Nat, +n: Nat, +side: Nat, +nbx: Nat) -> W.Fa:
  match d:
    case 0n:
      chunk(n, Nat.mod(i, nbx), Nat.div(i, nbx), side, W.F.cap0(U32.from_nat(Nat.add(n, 1n))))
    case 1n++j:
      a b = tree(j, Nat.mul(2n, i), n, side, nbx) tree(j, Nat.add(Nat.mul(2n, i), 1n), n, side, nbx)
      W.FaN{a, b}

def kc(k: P.K) -> P.K:
  P.K{g, mu, j, acc, size} = k
  P.K{g, mu, j, acc, size}

# zera as cabecas das celulas antes de remontar a grade
def clr(n: Nat, a: Array<U32>, +i: U32, +cap: U32) -> Array<U32>:
  match n:
    case 0n:
      a
    case 1n+m:
      clr(m, a[(W.F.hd(cap) + i : U32)] <- 0, (i + 1 : U32), cap)

# um tick: cada chunk remonta a sua grade e roda os seus corpos, todos ao
# mesmo tempo, cada um no seu array
def run2(f: W.Fa, +o: W.Og, +k: P.K, +mm: Nat) -> W.Fa:
  match f:
    case W.FaE{}:
      W.FaE{}
    case W.FaL{a, +nown, +nall, +cap}:
      W.FaL{W.F.ticks(U32.to_nat(nown), W.F.build(nall, clr(U32.to_nat(cap), a, 0, cap), cap, (cap - 1 : U32)),
        0, o, kc(k), cap, (cap - 1 : U32), nown, mm), nown, nall, cap}
    case W.FaN{lo, hi}:
      x y = run2(lo, o, k, mm) run2(hi, o, k, mm)
      W.FaN{x, y}

def ticks(t: Nat, f: W.Fa, +k: P.K, +mm: Nat) -> W.Fa:
  match t:
    case 0n:
      f
    case 1n+m:
      ticks(m, run2(f, W.Og{W.W.base(W.W.origin()), W.W.base(W.W.origin())}, k, mm), k, mm)

def count(f: W.Fa) -> Nat:
  match f:
    case W.FaE{}:
      0n
    case W.FaL{a, +nown, nall, cap}:
      U32.to_nat(nown)
    case W.FaN{lo, hi}:
      Nat.add(count(lo), count(hi))

def depth() -> Nat:
  8n

def per() -> Nat:
  392n

def side() -> Nat:
  14n

def main() -> IO(Unit):
  IO.print(Nat.show(Nat.mul(Nat.pow(2n, depth()), per())) ++ " cubos em " ++ Nat.show(Nat.pow(2n, depth()))
    ++ " chunks, 64 ticks, vivos " ++ Nat.show(count(ticks(64n, tree(depth(), 0n, per(), side(), 16n), k0(), 32768n))))
