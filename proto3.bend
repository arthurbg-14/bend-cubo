# prototipo 2: mundo em chunks persistentes, corpos ordenados por celula
import Base
import ./phys.bend as P
import ./world.bend as W
import ./main.bend as M

def k0() -> P.K:
  M.Knob.defaults()

def og() -> W.Og:
  W.Og{W.W.base(W.W.origin()), W.W.base(W.W.origin())}

# o corpo i do chunk (bx, bz): uma grade de cubos, um por celula, em tres
# camadas, tudo caindo
def body(+bx: Nat, +bz: Nat, +i: Nat) -> P.Body:
  +o = W.W.base(W.W.origin())
  P.Body{Nat.add(o, Nat.add(Nat.mul(Nat.add(Nat.mul(bx, 16n), Nat.mod(i, 14n)), 294912n), 16384n)),
    Nat.mul(Nat.add(Nat.div(i, 196n), 4n), 294912n),
    Nat.add(o, Nat.add(Nat.mul(Nat.add(Nat.mul(bz, 16n), Nat.mod(Nat.div(i, 14n), 14n)), 294912n), 16384n)),
    P.Pos{0n}, P.Pos{0n}, P.Pos{0n}, False{}, False{}}

def rows(+n: Nat, +bx: Nat, +bz: Nat) -> List<&2, P.Body>:
  match n:
    case 0n:
      []
    case 1n+m:
      body(bx, bz, m) <> rows(m, bx, bz)

def chunk(+n: Nat, +bx: Nat, +bz: Nat, r: U32 & Nat) -> W.Chk:
  (+cap, b) = r
  W.ChL{W.F.pack(rows(n, bx, bz), Array.new(U32, Nat.add(b, 5n), 0), 0, og(), False{}), U32.from_nat(n), cap,
    (U32.from_nat(Nat.mul(bx, 16n)) - 2 : U32), (U32.from_nat(Nat.mul(bz, 16n)) - 2 : U32)}

def tree(d: Nat, +i: Nat, +n: Nat, +nbx: Nat) -> W.Chk:
  match d:
    case 0n:
      chunk(n, Nat.mod(i, nbx), Nat.div(i, nbx), W.F.cap0(U32.from_nat(Nat.add(n, 1n))))
    case 1n++j:
      a b = tree(j, Nat.mul(2n, i), n, nbx) tree(j, Nat.add(Nat.mul(2n, i), 1n), n, nbx)
      W.ChN{a, b}

def ticks(t: Nat, f: W.Chk, +k: P.K, +mm: Nat) -> W.Chk:
  match t:
    case 0n:
      f
    case 1n+m:
      ticks(m, W.C.run(f, og(), k, mm), k, mm)

def count(f: W.Chk) -> Nat:
  match f:
    case W.ChE{}:
      0n
    case W.ChL{a, +n, cap, ox, oz}:
      U32.to_nat(n)
    case W.ChN{lo, hi}:
      Nat.add(count(lo), count(hi))

def depth() -> Nat:
  0n

def per() -> Nat:
  16n

def main() -> IO(Unit):
  IO.print(Nat.show(Nat.mul(Nat.pow(2n, depth()), per())) ++ " cubos em " ++ Nat.show(Nat.pow(2n, depth()))
    ++ " chunks, 64 ticks, vivos " ++ Nat.show(count(ticks(64n, tree(depth(), 0n, per(), 16n), k0(), 32768n))))
