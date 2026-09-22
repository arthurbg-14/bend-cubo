# Cubo -- proof optimizer, the profiler: every proof def of PROOF.bend
# checked on its own. The file is written once per proof with all the
# other proofs' bodies left as ?TODO (their statements stay, so whatever
# unfolds them still can), and the checker's time is what that one body
# costs. Defs that compute something keep their bodies: a proof may need
# to unfold them.

import Base
import ./core.bend as C

type Blk is Data:
  Blk{full: String, stub: String, proof: Bool, name: String}

type Tm is Data:
  Tm{idx: Nat, name: String, ms: Nat, st: String}

# ---- the statement a def makes ----

def arrow_at(+s: String, d: Nat) -> Bool:
  Bool.and(String.starts_with(s, "->"), Nat.is_eq(d, 0n))

def arrow_idx.go(s: String, here: Bool, +d: Nat, i: Nat) -> Maybe<&2, Nat>:
  match s here:
    case _ True{}:
      Some{i}
    case SNil{} False{}:
      None{}
    case SCon{+h, +t} False{}:
      arrow_idx.go(t, arrow_at(t, C.depth_step(h, d)), C.depth_step(h, d), 1n+i)

def arrow_idx(+s: String) -> Maybe<&2, Nat>:
  arrow_idx.go(s, arrow_at(s, 0n), 0n, 0n)

def drop_colon(+s: String) -> String:
  String.trim(String.take(s, Nat.sub(String.length(s), 1n)))

def ret_type.go(+sig: String, m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      SNil{}
    case Some{i}:
      drop_colon(String.trim(String.drop(sig, Nat.add(2n, i))))

def ret_type(+b: String) -> String:
  ret_type.go(C.sig_part(b), arrow_idx(C.sig_part(b)))

def head_of(+rt: String) -> String:
  C.first_of(C.tokens(rt))

def block_name(+b: String) -> String:
  String.trim(C.take_until_paren(String.drop(b, 4n)))

def is_def(+b: String) -> Bool:
  String.starts_with(b, "def ")

def is_type_rt(+rt: String) -> Bool:
  Bool.or(String.starts_with(rt, "Type"), String.starts_with(rt, "Kind"))

def type_level.pick(hit: Bool, +b: String, rest: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      block_name(b) <> rest
    case False{}:
      rest

# the defs that return a Type: FS, FREE, D, ... -- a proof's statement is one
def type_level(bs: List<&2, String>) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> r:
      type_level.pick(Bool.and(is_def(b), is_type_rt(ret_type(b))), b, type_level(r))

def is_proof.rt(+rt: String, +tl: List<&2, String>) -> Bool:
  Bool.or(String.starts_with(rt, "{"), Bool.or(C.mem(tl, head_of(rt)), String.eq(head_of(rt), "Empty")))

def is_proof.if(isdef: Bool, +b: String, +tl: List<&2, String>) -> Bool:
  match isdef:
    case True{}:
      Bool.or(String.starts_with(block_name(b), "Laws."), is_proof.rt(ret_type(b), tl))
    case False{}:
      False{}

def is_proof(+b: String, +tl: List<&2, String>) -> Bool:
  is_proof.if(is_def(b), b, tl)

# ---- one file per proof ----

def stub(+b: String) -> String:
  String.append(C.sig_part(b), "\n  ?TODO\n")

def blk.mk(proof: Bool, +b: String) -> Blk:
  match proof:
    case True{}:
      Blk{b, stub(b), True{}, block_name(b)}
    case False{}:
      Blk{b, b, False{}, SNil{}}

def blks(bs: List<&2, String>, +tl: List<&2, String>) -> List<&2, Blk>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> r:
      blk.mk(is_proof(b, tl), b) <> blks(r, tl)

def Blk.full(b: Blk) -> String:
  match b:
    case Blk{f, s, p, n}:
      f

def Blk.stub(b: Blk) -> String:
  match b:
    case Blk{f, s, p, n}:
      s

def Blk.proof(b: Blk) -> Bool:
  match b:
    case Blk{f, s, p, n}:
      p

def Blk.name(b: Blk) -> String:
  match b:
    case Blk{f, s, p, n}:
      n

def render.one(keep: Bool, +b: Blk) -> String:
  match keep:
    case True{}:
      Blk.full(b)
    case False{}:
      Blk.stub(b)

def render.go(bs: List<&2, Blk>, +k: Nat, +i: Nat) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> r:
      render.one(Nat.is_eq(i, k), b) <> render.go(r, k, 1n+i)

def render(+bs: List<&2, Blk>, +k: Nat) -> String:
  String.join(render.go(bs, k, 0n), "\n")

def proof_idx.pick(hit: Bool, i: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match hit:
    case True{}:
      i <> rest
    case False{}:
      rest

def proof_idx(bs: List<&2, Blk>, +i: Nat) -> List<&2, Nat>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> r:
      proof_idx.pick(Blk.proof(b), i, proof_idx(r, 1n+i))

def iso_path(+dir: String, +k: Nat) -> String:
  String.concat([dir, "/ISO_", Nat.show(k), ".bend"])

def write_isos(ks: List<&2, Nat>, +bs: List<&2, Blk>, +dir: String) -> IO(Unit):
  match ks:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +k <> r:
      do IO<Unit>:
        u : Unit <- C.write_all(iso_path(dir, k), render(bs, k))
        write_isos(r, bs, dir)

# ---- running them, many at once ----

def run_cmd(+dir: String, +glob: String, +par: Nat, +cap: Nat) -> String:
  String.concat(["cd '", dir, "' && ls ", glob, " | xargs -P ", Nat.show(par), " -I{} sh -c '",
    "ulimit -s 1000000 2>/dev/null; s=$(date +%s%N); ",
    "o=$(BEND_NO_TELEMETRY=1 BUN_JSC_maxPerThreadStackUsage=805306368 timeout ", Nat.show(cap),
    " ${BEND:-$HOME/.bend/bin/bend} --check-only {} 2>&1); c=$?; e=$(date +%s%N); ",
    "if [ $c = 124 ]; then st=timeout; elif printf \"%s\" \"$o\" | grep -q \"^- \\(expected\\|observed\\|message\\)\"; ",
    "then st=fail; else st=ok; fi; echo \"{} $(( (e - s) / 1000000 )) $st\"; rm -f {}'"])

# ISO_12.bend, LIFT_3.bend: the number after the last _
def iso_idx(+f: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(C.last_of(String.split(C.first_of(String.split(f, '.')), '_'))), 0n)

def tm_of.go(+ws: List<&2, String>) -> Tm:
  Tm{iso_idx(C.nth(ws, 0n)), SNil{}, Maybe.default(&2, Nat, Nat.read(C.nth(ws, 1n)), 0n), C.nth(ws, 2n)}

def tm_of(+line: String) -> Tm:
  tm_of.go(String.split(String.trim(line), ' '))

def tms.pick(hit: Bool, +l: String, rest: List<&2, Tm>) -> List<&2, Tm>:
  match hit:
    case True{}:
      tm_of(l) <> rest
    case False{}:
      rest

def tms(ls: List<&2, String>) -> List<&2, Tm>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> r:
      tms.pick(String.contains(l, ".bend "), l, tms(r))

def Tm.idx(t: Tm) -> Nat:
  match t:
    case Tm{i, n, m, s}:
      i

def Tm.name(t: Tm) -> String:
  match t:
    case Tm{i, n, m, s}:
      n

def Tm.ms(t: Tm) -> Nat:
  match t:
    case Tm{i, n, m, s}:
      m

def Tm.st(t: Tm) -> String:
  match t:
    case Tm{i, n, m, s}:
      s

def blk_name_at(bs: List<&2, Blk>, n: Nat) -> String:
  match bs n:
    case Nil{} _:
      SNil{}
    case Con{b, r} 0n:
      Blk.name(b)
    case Con{b, r} 1n+m:
      blk_name_at(r, m)

def named(ts: List<&2, Tm>, +bs: List<&2, Blk>) -> List<&2, Tm>:
  match ts:
    case Nil{}:
      Nil{}
    case +t <> r:
      Tm{Tm.idx(t), blk_name_at(bs, Tm.idx(t)), Tm.ms(t), Tm.st(t)} <> named(r, bs)

# ---- sorting, slowest first ----

def head_le(ts: List<&2, Tm>, +t: Tm) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case +h <> r:
      Nat.is_le(Tm.ms(h), Tm.ms(t))

def ins_tm.go(ts: List<&2, Tm>, before: Bool, +t: Tm) -> List<&2, Tm>:
  match ts before:
    case Nil{} _:
      [t]
    case Con{h, r} True{}:
      t <> (h <> r)
    case Con{h, +r} False{}:
      h <> ins_tm.go(r, head_le(r, t), t)

def ins_tm(+ts: List<&2, Tm>, +t: Tm) -> List<&2, Tm>:
  ins_tm.go(ts, head_le(ts, t), t)

def sort_tm(ts: List<&2, Tm>) -> List<&2, Tm>:
  match ts:
    case Nil{}:
      Nil{}
    case h <> r:
      ins_tm(sort_tm(r), h)

# ---- the profile ----

def profile.go(+dir: String, +par: Nat, +cap: Nat, +bs: List<&2, Blk>, +ks: List<&2, Nat>) -> IO(List<&2, Tm>):
  do IO<List<&2, Tm>>:
    u : Unit <- write_isos(ks, bs, dir)
    out : String <- IO.try(String, C.Sys.run(run_cmd(dir, "ISO_*.bend", par, cap)))
    return sort_tm(named(tms(String.lines(out)), bs))

def proof_idx_in(bs: List<&2, Blk>, +names: List<&2, String>, +i: Nat) -> List<&2, Nat>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> r:
      proof_idx.pick(Bool.and(Blk.proof(b), C.mem(names, Blk.name(b))), i, proof_idx_in(r, names, 1n+i))

def proof_blks(+proof: String) -> List<&2, Blk>:
  blks(C.blocks(proof), type_level(C.blocks(proof)))

# every proof block of <dir>/PROOF.bend, timed on its own
def profile(+dir: String, +par: Nat, +cap: Nat) -> IO(List<&2, Tm>):
  do IO<List<&2, Tm>>:
    +bs : List<&2, Blk> <- IO.bind(String, List<&2, Blk>, C.read_all(String.append(dir, "/PROOF.bend")),
      (p: String) => IO.pure(List<&2, Blk>, proof_blks(p)))
    profile.go(dir, par, cap, bs, proof_idx(bs, 0n))

# only the proofs named
def profile.only(+dir: String, +names: List<&2, String>, +par: Nat, +cap: Nat) -> IO(List<&2, Tm>):
  do IO<List<&2, Tm>>:
    +bs : List<&2, Blk> <- IO.bind(String, List<&2, Blk>, C.read_all(String.append(dir, "/PROOF.bend")),
      (p: String) => IO.pure(List<&2, Blk>, proof_blks(p)))
    profile.go(dir, par, cap, bs, proof_idx_in(bs, names, 0n))

def tm_line(+t: Tm) -> String:
  String.concat([Nat.show(Tm.ms(t)), " ms  ", Tm.name(t), "  ", Tm.st(t)])

def tm_lines(ts: List<&2, Tm>) -> List<&2, String>:
  match ts:
    case Nil{}:
      Nil{}
    case +t <> r:
      tm_line(t) <> tm_lines(r)

def total_ms(ts: List<&2, Tm>) -> Nat:
  match ts:
    case Nil{}:
      0n
    case +t <> r:
      Nat.add(Tm.ms(t), total_ms(r))

def bad_count(ts: List<&2, Tm>) -> Nat:
  match ts:
    case Nil{}:
      0n
    case +t <> r:
      Nat.add(Bool.pick(Nat, String.eq(Tm.st(t), "ok"), 0n, 1n), bad_count(r))
