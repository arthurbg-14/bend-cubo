# Cubo -- proof optimizer.
#
#   bend tools/optimize.bend auto <dir> [par] [cap]
#     the whole search: profile, try every rewrite the slow proofs point
#     at, keep what checks and helps, check all of PROOF.bend before/after
#   bend tools/optimize.bend cands <dir> <proof>...
#     the rewrites auto would try for those proofs
#   bend tools/optimize.bend profile <dir> [par] [cap]
#     every proof def of <dir>/PROOF.bend checked on its own, slowest first
#   bend tools/optimize.bend hoist <dir> <Def> <let> <Type>
#     turns the let into a parameter of <Def> (see opt/core.bend)
#   bend tools/optimize.bend lift <dir> <Def> [par] [cap]
#     takes out of <Def>'s match the record fields every branch agrees on,
#     as far as the checker proves it (see opt/lift.bend)
#   bend tools/optimize.bend pair <dir> <Def> [cap]
#     <Def> takes its decision and the record it is about as one pair,
#     once the checker proves it equal to the old one (see opt/pair.bend)
#   bend tools/optimize.bend once <dir> <Lemma> [hot,...] [cap]
#     <Lemma> and the lemmas its proof ends in state their claim about a
#     record through Once, which opens it once (see opt/once.bend)
#
# Rewrites happen in place, so run them on a copy. Run from the repo root;
# it calls the bend on $BEND, else ~/.bend/bin/bend.

import Base
import ./opt/core.bend as C
import ./opt/hoist.bend as H
import ./opt/prof.bend as F
import ./opt/lift.bend as L
import ./opt/auto.bend as A
import ./opt/pair.bend as P
import ./opt/once.bend as O

def arg_nat(+a: List<&2, String>, i: Nat, d: Nat) -> Nat:
  Maybe.default(&2, Nat, Nat.read(C.nth(a, i)), d)

def do_profile(+dir: String, +par: Nat, +cap: Nat) -> IO(Unit):
  do IO<Unit>:
    +ts : List<&2, F.Tm> <- F.profile(dir, par, cap)
    u : Unit <- IO.print(String.join(F.tm_lines(ts), "\n"))
    IO.print(String.concat([Nat.show(List.length(&2, F.Tm, ts)), " proofs, ", Nat.show(F.total_ms(ts)),
      " ms in all, ", Nat.show(F.bad_count(ts)), " not ok"]))

def usage() -> IO(Unit):
  IO.print(String.concat(["usage:\n",
    "  bend tools/optimize.bend auto <dir> [par=12] [cap=900]\n",
    "  bend tools/optimize.bend cands <dir> <proof>...\n",
    "  bend tools/optimize.bend profile <dir> [par=12] [cap=900]\n",
    "  bend tools/optimize.bend hoist <dir> <Def> <let> <Type>\n",
    "  bend tools/optimize.bend lift <dir> <Def> [par=12] [cap=300]\n",
    "  bend tools/optimize.bend pair <dir> <Def> [cap=900]\n",
    "  bend tools/optimize.bend once <dir> <Lemma> [hot,...] [cap=900]"]))

def do_lift(+dir: String, +d: String, +par: Nat, +cap: Nat) -> IO(Unit):
  do IO<Unit>:
    msg : String <- L.lift(dir, d, par, cap)
    IO.print(msg)

def rest_after(n: Nat, xs: List<&2, String>) -> List<&2, String>:
  match n xs:
    case 0n _:
      xs
    case 1n+m Nil{}:
      Nil{}
    case 1n+m Con{h, t}:
      rest_after(m, t)

def do_pair(+dir: String, +d: String, +cap: Nat) -> IO(Unit):
  do IO<Unit>:
    msg : String <- P.pair(dir, d, cap)
    IO.print(msg)

def do_once(+dir: String, +l: String, +hot: List<&2, String>, +cap: Nat) -> IO(Unit):
  do IO<Unit>:
    msg : String <- O.once(dir, l, hot, cap)
    IO.print(msg)

def run.once(once: Bool, +a: List<&2, String>) -> IO(Unit):
  match once:
    case True{}:
      do_once(C.nth(a, 1n), C.nth(a, 2n), String.split(C.nth(a, 3n), ','), arg_nat(a, 4n, 900n))
    case False{}:
      usage()

def run.pair(pair: Bool, +a: List<&2, String>) -> IO(Unit):
  match pair:
    case True{}:
      do_pair(C.nth(a, 1n), C.nth(a, 2n), arg_nat(a, 3n, 900n))
    case False{}:
      run.once(Bool.and(String.eq(C.nth(a, 0n), "once"), Nat.is_le(3n, List.length(&2, String, a))), a)

def run.cands(cands: Bool, +a: List<&2, String>) -> IO(Unit):
  match cands:
    case True{}:
      A.cands(C.nth(a, 1n), rest_after(2n, a))
    case False{}:
      run.pair(Bool.and(String.eq(C.nth(a, 0n), "pair"), Nat.is_le(3n, List.length(&2, String, a))), a)

def run.auto(auto: Bool, +a: List<&2, String>) -> IO(Unit):
  match auto:
    case True{}:
      A.auto(C.nth(a, 1n), arg_nat(a, 2n, 12n), arg_nat(a, 3n, 900n))
    case False{}:
      run.cands(Bool.and(String.eq(C.nth(a, 0n), "cands"), Nat.is_le(3n, List.length(&2, String, a))), a)

def run.lift(lift: Bool, +a: List<&2, String>) -> IO(Unit):
  match lift:
    case True{}:
      do_lift(C.nth(a, 1n), C.nth(a, 2n), arg_nat(a, 3n, 12n), arg_nat(a, 4n, 300n))
    case False{}:
      run.auto(Bool.and(String.eq(C.nth(a, 0n), "auto"), Nat.is_le(2n, List.length(&2, String, a))), a)

def run.profile(profile: Bool, +a: List<&2, String>) -> IO(Unit):
  match profile:
    case True{}:
      do_profile(C.nth(a, 1n), arg_nat(a, 2n, 12n), arg_nat(a, 3n, 900n))
    case False{}:
      run.lift(Bool.and(String.eq(C.nth(a, 0n), "lift"), Nat.is_le(3n, List.length(&2, String, a))), a)

def run.hoist(hoist: Bool, profile: Bool, +a: List<&2, String>) -> IO(Unit):
  match hoist:
    case True{}:
      H.hoist(C.nth(a, 1n), C.nth(a, 2n), C.nth(a, 3n), C.nth(a, 4n))
    case False{}:
      run.profile(profile, a)

def run.go(+cmd: String, +a: List<&2, String>) -> IO(Unit):
  run.hoist(Bool.and(String.eq(cmd, "hoist"), Nat.is_le(5n, List.length(&2, String, a))),
    Bool.and(String.eq(cmd, "profile"), Nat.is_le(2n, List.length(&2, String, a))), a)

def run(+a: List<&2, String>) -> IO(Unit):
  run.go(C.nth(a, 0n), a)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    run(C.to2(args))
