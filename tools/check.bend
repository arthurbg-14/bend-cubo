# Cubo -- the proofs, checked in parallel.
#
#   bend tools/check.bend [dir=.] [parts=16] [par=8]
#
# PROOF.bend is cut into parts, each the whole file except that every
# proof's body is real in exactly one part and ?TODO in the others; the
# parts are checked at the same time. The verdict is the one of
# `bend PROOF.bend`: every body is checked once, against the same
# statements and the same defs in the same order. Bend takes a name only
# below its def, so a proof that leans on itself through other proofs
# still needs a use above a def, in a body some part checks. PROOF.bend
# may hold no ?TODO or @unsafe of its own, so every TODO a part reports is
# one of its stubs or a law with no proof, and those laws are named.
# Exits 1 unless every proof checks and every law has one.

import Base
import ./opt/core.bend as C
import ./opt/prof.bend as F

def arg_nat(+a: List<&2, String>, i: Nat, d: Nat) -> Nat:
  Maybe.default(&2, Nat, Nat.read(C.nth(a, i)), d)

# ---- the parts ----

type Pz is Data:
  Pz{name: String, size: Nat}

def Pz.name(p: Pz) -> String:
  match p:
    case Pz{n, s}:
      n

def Pz.size(p: Pz) -> Nat:
  match p:
    case Pz{n, s}:
      s

type Part is Data:
  Part{load: Nat, names: List<&2, String>}

def Part.load(p: Part) -> Nat:
  match p:
    case Part{l, ns}:
      l

def Part.names(p: Part) -> List<&2, String>:
  match p:
    case Part{l, ns}:
      ns

def pz.pick(proof: Bool, +b: F.Blk, rest: List<&2, Pz>) -> List<&2, Pz>:
  match proof:
    case True{}:
      Pz{F.Blk.name(b), String.length(F.Blk.full(b))} <> rest
    case False{}:
      rest

# every proof and how long its block is: the guess at what it costs
def pzs(bs: List<&2, F.Blk>) -> List<&2, Pz>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> r:
      pz.pick(F.Blk.proof(b), b, pzs(r))

def head_ge(ps: List<&2, Pz>, +p: Pz) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case +h <> r:
      Nat.is_le(Pz.size(h), Pz.size(p))

def ins_pz(ps: List<&2, Pz>, before: Bool, +p: Pz) -> List<&2, Pz>:
  match ps before:
    case Nil{} _:
      [p]
    case Con{h, r} True{}:
      p <> (h <> r)
    case Con{h, +r} False{}:
      h <> ins_pz(r, head_ge(r, p), p)

def ins_pz.top(+ps: List<&2, Pz>, +p: Pz) -> List<&2, Pz>:
  ins_pz(ps, head_ge(ps, p), p)

# biggest first
def sort_pz(ps: List<&2, Pz>) -> List<&2, Pz>:
  match ps:
    case Nil{}:
      Nil{}
    case h <> r:
      ins_pz.top(sort_pz(r), h)

def empty_parts(k: Nat) -> List<&2, Part>:
  match k:
    case 0n:
      Nil{}
    case 1n+m:
      Part{0n, Nil{}} <> empty_parts(m)

def min_load(ps: List<&2, Part>) -> Nat:
  match ps:
    case Nil{}:
      0n
    case +p <> Nil{}:
      Part.load(p)
    case +p <> r:
      Nat.min(Part.load(p), min_load(r))

def head_at(ps: List<&2, Part>, +m: Nat) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case +p <> r:
      Nat.is_eq(Part.load(p), m)

def add_first(ps: List<&2, Part>, +m: Nat, +z: Pz, here: Bool) -> List<&2, Part>:
  match ps here:
    case Nil{} _:
      Nil{}
    case Con{+p, r} True{}:
      Part{Nat.add(Part.load(p), Pz.size(z)), Pz.name(z) <> Part.names(p)} <> r
    case Con{p, +r} False{}:
      p <> add_first(r, m, z, head_at(r, m))

# each proof, biggest first, into the lightest part
def spread(zs: List<&2, Pz>, +ps: List<&2, Part>) -> List<&2, Part>:
  match zs:
    case Nil{}:
      ps
    case +z <> r:
      spread(r, add_first(ps, min_load(ps), z, head_at(ps, min_load(ps))))

def render.one(+b: F.Blk, +keep: List<&2, String>) -> String:
  Bool.pick(String, Bool.and(F.Blk.proof(b), Bool.not(C.mem(keep, F.Blk.name(b)))), F.Blk.stub(b), F.Blk.full(b))

def render.go(bs: List<&2, F.Blk>, +keep: List<&2, String>) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> r:
      render.one(b, keep) <> render.go(r, keep)

def part_path(+dir: String, +i: Nat) -> String:
  String.concat([dir, "/CHK_", Nat.show(i), ".bend"])

def write_parts(ps: List<&2, Part>, +bs: List<&2, F.Blk>, +dir: String, +i: Nat) -> IO(Unit):
  match ps:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +p <> r:
      do IO<Unit>:
        u : Unit <- C.write_all(part_path(dir, i), String.join(render.go(bs, Part.names(p)), "\n"))
        write_parts(r, bs, dir, 1n+i)

def part_paths(n: Nat, +dir: String, +i: Nat) -> List<&2, String>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      part_path(dir, i) <> part_paths(m, dir, 1n+i)

# ---- what must not be there, and the laws with no proof ----

# a line without its comment
def code_of(+l: String) -> String:
  String.take(l, C.or_len(C.find(l, "#"), String.length(l)))

def has_code.pick(hit: Bool, rest: Bool) -> Bool:
  match hit:
    case True{}:
      True{}
    case False{}:
      rest

# pat in a line's code, not in its comment
def has_code(ls: List<&2, String>, +pat: String) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case +l <> r:
      has_code.pick(String.contains(code_of(l), pat), has_code(r, pat))

def law_name(+l: String) -> String:
  String.trim(C.first_of(String.split(String.drop(l, 4n), ':')))

def open.pick(hit: Bool, +n: String, rest: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      n <> rest
    case False{}:
      rest

def proof_names(bs: List<&2, F.Blk>) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> r:
      open.pick(F.Blk.proof(b), F.Blk.name(b), proof_names(r))

# the laws of LAWS.bend with no Laws.<name> among the proofs
def open_laws(ls: List<&2, String>, +have: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> r:
      open.pick(Bool.and(String.starts_with(l, "law "), Bool.not(C.mem(have, String.append("Laws.", law_name(l))))),
        law_name(l), open_laws(r, have))

# ---- the verdict ----

type Res is Data:
  Res{idx: Nat, st: String, n: Nat}

def Res.idx(r: Res) -> Nat:
  match r:
    case Res{i, s, n}:
      i

def Res.st(r: Res) -> String:
  match r:
    case Res{i, s, n}:
      s

def Res.n(r: Res) -> Nat:
  match r:
    case Res{i, s, n}:
      n

# "CHK_3.bend <ms> <status> <TODOs>"
def res_of(+ws: List<&2, String>) -> Res:
  Res{F.iso_idx(C.nth(ws, 0n)), C.nth(ws, 2n), Maybe.default(&2, Nat, Nat.read(C.nth(ws, 3n)), 0n)}

def ress.pick(hit: Bool, +l: String, rest: List<&2, Res>) -> List<&2, Res>:
  match hit:
    case True{}:
      res_of(String.split(String.trim(l), ' ')) <> rest
    case False{}:
      rest

def ress(ls: List<&2, String>) -> List<&2, Res>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> r:
      ress.pick(String.contains(l, ".bend "), l, ress(r))

def part_at(ps: List<&2, Part>, n: Nat) -> List<&2, String>:
  match ps n:
    case Nil{} _:
      Nil{}
    case Con{p, r} 0n:
      Part.names(p)
    case Con{p, r} 1n+m:
      part_at(r, m)

# the TODOs part i has to report: one per proof it stubs, one per open law
def expected(+ps: List<&2, Part>, +i: Nat, +total: Nat, +open: Nat) -> Nat:
  Nat.add(Nat.sub(total, List.length(&2, String, part_at(ps, i))), open)

def fine(+r: Res, +ps: List<&2, Part>, +total: Nat, +open: Nat) -> Bool:
  Bool.and(Bool.or(String.eq(Res.st(r), "ok"), String.eq(Res.st(r), "todo")), Nat.is_eq(Res.n(r), expected(ps, Res.idx(r), total, open)))

def bad.pick(bad: Bool, +r: Res, rest: List<&2, Res>) -> List<&2, Res>:
  match bad:
    case True{}:
      r <> rest
    case False{}:
      rest

# a part is fine when it checks with its stubs and the open laws as its only TODOs
def bad_parts(rs: List<&2, Res>, +ps: List<&2, Part>, +total: Nat, +open: Nat) -> List<&2, Res>:
  match rs:
    case Nil{}:
      Nil{}
    case +r <> t:
      bad.pick(Bool.not(fine(r, ps, total, open)), r, bad_parts(t, ps, total, open))

def err_line(+l: String) -> Bool:
  Bool.or(String.starts_with(l, "- "), Bool.or(String.starts_with(l, "Location"), String.contains(l, ">|")))

def cut(+l: String) -> String:
  Bool.pick(String, Nat.is_lt(300n, String.length(l)), String.append(String.take(l, 300n), " ..."), l)

def err_lines.pick(hit: Bool, +l: String, rest: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      cut(l) <> rest
    case False{}:
      rest

def err_lines(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> r:
      err_lines.pick(err_line(l), l, err_lines(r))

def show.one(failed: Bool, +r: Res, +dir: String, +want: Nat) -> IO(Unit):
  match failed:
    case True{}:
      do IO<Unit>:
        +err : String <- C.read_all(String.append(part_path(dir, Res.idx(r)), ".err"))
        IO.print(String.concat(["part ", Nat.show(Res.idx(r)), ": ", Res.st(r), " (line numbers are the part's)\n",
          String.join(List.take(&2, String, err_lines(String.lines(err)), 24n), "\n")]))
    case False{}:
      IO.print(String.concat(["part ", Nat.show(Res.idx(r)), ": ", Nat.show(Res.n(r)), " TODOs where its stubs and the open laws make ",
        Nat.show(want), ": a ?TODO outside PROOF.bend's proofs"]))

def show_bad(rs: List<&2, Res>, +dir: String, +ps: List<&2, Part>, +total: Nat, +open: Nat) -> IO(Unit):
  match rs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +r <> t:
      do IO<Unit>:
        u : Unit <- show.one(Bool.or(String.eq(Res.st(r), "fail"), String.eq(Res.st(r), "timeout")), r, dir, expected(ps, Res.idx(r), total, open))
        show_bad(t, dir, ps, total, open)

def sh(+cmd: String) -> IO(Unit):
  do IO<Unit>:
    out : String <- IO.try(String, C.Sys.run(cmd))
    return Unit{}

def wall_ms(+out: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(C.nth(String.split(C.first_of(String.lines(out)), ' '), 1n)), 0n)

def secs(+ms: Nat) -> String:
  String.concat([Nat.show(Nat.div(ms, 1000n)), ".", Nat.show(Nat.div(Nat.mod(ms, 1000n), 100n)), "s"])

def finish(+bad: List<&2, Res>, +open: List<&2, String>, +dir: String, +head: String, +ps: List<&2, Part>, +total: Nat) -> IO(Unit):
  do IO<Unit>:
    u0 : Unit <- IO.print(head)
    u1 : Unit <- show_bad(bad, dir, ps, total, List.length(&2, String, open))
    u2 : Unit <- sh(String.concat(["rm -f '", dir, "'/CHK_*.bend.err"]))
    u3 : Unit <- IO.print(Bool.pick(String, List.is_empty(&2, String, open), "every law has a proof",
      String.concat([Nat.show(List.length(&2, String, open)), " laws still open: ", String.join(open, ", ")])))
    C.guard(Bool.and(List.is_empty(&2, Res, bad), List.is_empty(&2, String, open)), "PROOF.bend does not hold")

def run.go(+dir: String, +k: Nat, +par: Nat, +cap: Nat, +bs: List<&2, F.Blk>, +ps: List<&2, Part>, +open: List<&2, String>) -> IO(Unit):
  +total = List.length(&2, Pz, pzs(bs))
  do IO<Unit>:
    u : Unit <- write_parts(ps, bs, dir, 0n)
    +out : String <- IO.try(String, C.Sys.run(F.run_paths(part_paths(k, dir, 0n), par, cap)))
    finish(bad_parts(ress(String.lines(out)), ps, total, List.length(&2, String, open)), open, dir,
      String.concat(["PROOF.bend: ", Nat.show(total), " proofs in ", Nat.show(k), " parts, ", Nat.show(par), " at a time: ",
        secs(wall_ms(out)), "; ", Nat.show(List.length(&2, Res, bad_parts(ress(String.lines(out)), ps, total, List.length(&2, String, open)))),
        " parts failed"]), ps, total)

def run(+dir: String, +k: Nat, +par: Nat, +cap: Nat, +proof: String, +laws: String) -> IO(Unit):
  +bs = F.proof_blks(proof)
  run.go(dir, k, par, cap, bs, spread(sort_pz(pzs(bs)), empty_parts(k)), open_laws(String.lines(laws), proof_names(bs)))

def clean(ok: Bool, +dir: String, +k: Nat, +par: Nat, +cap: Nat, +proof: String, +laws: String) -> IO(Unit):
  match ok:
    case True{}:
      run(dir, k, par, cap, proof, laws)
    case False{}:
      IO.die(Unit, 1, "PROOF.bend holds a ?TODO or an @unsafe: check it whole with `bend PROOF.bend`")

def check(+dir: String, +k: Nat, +par: Nat, +cap: Nat) -> IO(Unit):
  do IO<Unit>:
    +proof : String <- C.read_all(String.append(dir, "/PROOF.bend"))
    +laws : String <- C.read_all(String.append(dir, "/LAWS.bend"))
    clean(Bool.not(Bool.or(has_code(String.lines(proof), "?TODO"), has_code(String.lines(proof), "@unsafe"))), dir, k, par, cap, proof, laws)

def dir_of(+a: List<&2, String>) -> String:
  Bool.pick(String, String.is_empty(C.nth(a, 0n)), ".", C.nth(a, 0n))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    +a : List<&2, String> = C.to2(args)
    check(dir_of(a), Nat.max(1n, arg_nat(a, 1n, 16n)), Nat.max(1n, arg_nat(a, 2n, 8n)), 1800n)
