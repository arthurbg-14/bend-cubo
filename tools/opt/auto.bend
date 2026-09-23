# Cubo -- proof optimizer, the search: every proof of PROOF.bend is timed;
# the slow ones (at least 3x the median) point at the phys defs their
# statements unfold, and every rewrite those defs admit (a let turned into a
# parameter, record fields lifted out of a match, a decision paired with its
# record) and the slow lemmas admit (claims about a record stated once, a
# call that repeats a stuck record moved into a lemma of its own) is
# tried on a copy. The proofs a rewrite touches (all of them, when it
# changes phys.bend) are then checked old and new side by side (one at a
# time, unless it is all of them); it stays only if nothing fails and they
# got at least 5% faster, and the search starts over from the new times.
# Last, the whole of PROOF.bend is checked before and after.

import Base
import ./core.bend as C
import ./hoist.bend as H
import ./prof.bend as F
import ./lift.bend as L
import ./calls.bend as K
import ./pair.bend as P
import ./once.bend as O
import ./abst.bend as B

type Cand is Data:
  Hoist{d: String, l: String, t: String}
  LiftC{d: String}
  PairC{d: String}
  OnceC{roots: List<&2, String>, hot: List<&2, String>}
  AbstC{l: String}

type St is Data:
  St{times: List<&2, F.Tm>, tried: List<&2, String>, kept: List<&2, String>, gained: Bool}

# ---- names ----

def cand_key(c: Cand) -> String:
  match c:
    case Hoist{d, l, t}:
      String.concat(["hoist ", d, " ", l])
    case LiftC{d}:
      String.append("lift ", d)
    case PairC{d}:
      String.append("pair ", d)
    case OnceC{rs, hs}:
      String.append("once ", String.join(rs, ","))
    case AbstC{l}:
      String.append("abst ", l)

def uniq.pick(dup: Bool, +h: String, rest: List<&2, String>) -> List<&2, String>:
  match dup:
    case True{}:
      rest
    case False{}:
      h <> rest

def uniq(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case +h <> +t:
      uniq.pick(C.mem(t, h), h, uniq(t))

def def_block(+bs: List<&2, String>, +d: String) -> String:
  C.find_block(bs, String.concat(["def ", d, "("]))

def is_def_in(+bs: List<&2, String>, +d: String) -> Bool:
  Bool.not(String.is_empty(def_block(bs, d)))

# ---- the slow proofs ----

def hot.pick(hit: Bool, +t: F.Tm, rest: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      F.Tm.name(t) <> rest
    case False{}:
      rest

def tm_at(ts: List<&2, F.Tm>, n: Nat) -> Nat:
  match ts n:
    case Nil{} _:
      0n
    case Con{t, r} 0n:
      F.Tm.ms(t)
    case Con{t, r} 1n+m:
      tm_at(r, m)

# the time half the proofs stay under
def median_ms(+ts: List<&2, F.Tm>) -> Nat:
  tm_at(ts, Nat.div(List.length(&2, F.Tm, ts), 2n))

# proofs at or above min ms, and never more than n of them (times come sorted)
def hot(n: Nat, ts: List<&2, F.Tm>, +min: Nat) -> List<&2, String>:
  match n ts:
    case 0n _:
      Nil{}
    case 1n+m Nil{}:
      Nil{}
    case 1n+m Con{+t, r}:
      hot.pick(Nat.is_le(min, F.Tm.ms(t)), t, hot(m, r, min))

def fails(ts: List<&2, F.Tm>) -> Nat:
  match ts:
    case Nil{}:
      0n
    case +t <> r:
      Nat.add(Bool.pick(Nat, String.eq(F.Tm.st(t), "fail"), 1n, 0n), fails(r))

def find_tm(ts: List<&2, F.Tm>, +n: String, +old: F.Tm) -> F.Tm:
  match ts:
    case Nil{}:
      old
    case +t <> r:
      Bool.pick(F.Tm, String.eq(F.Tm.name(t), n), t, find_tm(r, n, old))

# the old times, with every proof measured again replaced
def merge(cur: List<&2, F.Tm>, +new: List<&2, F.Tm>) -> List<&2, F.Tm>:
  match cur:
    case Nil{}:
      Nil{}
    case +t <> r:
      find_tm(new, F.Tm.name(t), t) <> merge(r, new)

# ---- what the slow proofs point at ----

def pre_drop.pick(hit: Bool, +t: String, +pre: String, rest: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      String.drop(t, String.length(pre)) <> rest
    case False{}:
      rest

def pre_drop(ts: List<&2, String>, +pre: String) -> List<&2, String>:
  match ts:
    case Nil{}:
      Nil{}
    case +t <> r:
      pre_drop.pick(String.starts_with(t, pre), t, pre, pre_drop(r, pre))

# the phys defs a proof's statement names, P.X( giving X
def stmt_defs(hot: List<&2, String>, +pbs: List<&2, String>, +al: String) -> List<&2, String>:
  match hot:
    case Nil{}:
      Nil{}
    case +n <> r:
      List.append(&2, String, pre_drop(C.tokens(C.sig_part(def_block(pbs, n))), String.append(al, ".")),
        stmt_defs(r, pbs, al))

def keep_defs.pick(hit: Bool, +t: String, rest: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      t <> rest
    case False{}:
      rest

def keep_defs(ts: List<&2, String>, +bs: List<&2, String>) -> List<&2, String>:
  match ts:
    case Nil{}:
      Nil{}
    case +t <> r:
      keep_defs.pick(is_def_in(bs, t), t, keep_defs(r, bs))

# the phys defs a phys def calls
def callees(ds: List<&2, String>, +bs: List<&2, String>) -> List<&2, String>:
  match ds:
    case Nil{}:
      Nil{}
    case +d <> r:
      List.append(&2, String, keep_defs(C.tokens(String.drop(def_block(bs, d), 4n)), bs), callees(r, bs))

# ---- the lets of a def, and their types ----

def simple_ident(+x: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(x)), String.eq(C.first_of(C.tokens(x)), x))

def let_name.go(+t: String) -> String:
  C.strip_q(String.trim(String.take(t, C.or_len(C.find(t, " = "), 0n))))

def let_name(+line: String) -> String:
  Bool.pick(String, String.contains(String.trim(line), " = "), let_name.go(String.trim(line)), SNil{})

def lets.pick(hit: Bool, +n: String, rest: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      n <> rest
    case False{}:
      rest

def lets(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> r:
      lets.pick(simple_ident(let_name(l)), let_name(l), lets(r))

# the type a let has: what the def its value calls answers
def let_type(+bs: List<&2, String>, +base: List<&2, String>, +expr: String) -> String:
  Bool.pick(String, is_def_in(bs, C.first_of(C.tokens(expr))),
    F.ret_type(def_block(bs, C.first_of(C.tokens(expr)))),
    F.ret_type(def_block(base, C.first_of(C.tokens(expr)))))

def hoists.pick(ok: Bool, +d: String, +l: String, +t: String, rest: List<&2, Cand>) -> List<&2, Cand>:
  match ok:
    case True{}:
      Hoist{d, l, t} <> rest
    case False{}:
      rest

def hoists.of(ls: List<&2, String>, +d: String, +body: List<&2, String>, +bs: List<&2, String>, +base: List<&2, String>) -> List<&2, Cand>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> r:
      hoists.pick(simple_ident(let_type(bs, base, C.let_expr(body, l))), d, l, let_type(bs, base, C.let_expr(body, l)),
        hoists.of(r, d, body, bs, base))

def hoists(ds: List<&2, String>, +bs: List<&2, String>, +base: List<&2, String>) -> List<&2, Cand>:
  match ds:
    case Nil{}:
      Nil{}
    case +d <> r:
      List.append(&2, Cand, hoists.of(lets(L.body_lines(def_block(bs, d))), d, L.body_lines(def_block(bs, d)), bs, base),
        hoists(r, bs, base))

def lifts.pick(ok: Bool, +d: String, rest: List<&2, Cand>) -> List<&2, Cand>:
  match ok:
    case True{}:
      LiftC{d} <> rest
    case False{}:
      rest

def lifts(ds: List<&2, String>, +bs: List<&2, String>) -> List<&2, Cand>:
  match ds:
    case Nil{}:
      Nil{}
    case +d <> r:
      lifts.pick(L.Lift.ok(L.read_lift(d, bs)), d, lifts(r, bs))

def pairs.pick(ok: Bool, +d: String, rest: List<&2, Cand>) -> List<&2, Cand>:
  match ok:
    case True{}:
      PairC{d} <> rest
    case False{}:
      rest

def pairs(ds: List<&2, String>, +bs: List<&2, String>, +recs: List<&2, K.Rec>) -> List<&2, Cand>:
  match ds:
    case Nil{}:
      Nil{}
    case +d <> r:
      pairs.pick(P.pair.fits(def_block(bs, d), d, recs), d, pairs(r, bs, recs))

def onces.of(empty: Bool, +rs: List<&2, String>, +hot: List<&2, String>) -> List<&2, Cand>:
  match empty:
    case True{}:
      Nil{}
    case False{}:
      [OnceC{rs, hot}]

# the chains of the slow lemmas, stated once, as one rewrite
def onces(+hot: List<&2, String>, +phys: String, +proof: String) -> List<&2, Cand>:
  onces.of(List.is_empty(&2, String, O.roots(hot, phys, proof)), O.roots(hot, phys, proof), hot)

def absts.pick(ok: Bool, +l: String, rest: List<&2, Cand>) -> List<&2, Cand>:
  match ok:
    case True{}:
      AbstC{l} <> rest
    case False{}:
      rest

# the slow lemmas with a call that repeats a stuck record
def absts(hot: List<&2, String>, +phys: String, +proof: String, +base: String) -> List<&2, Cand>:
  match hot:
    case Nil{}:
      Nil{}
    case +l <> r:
      absts.pick(B.abst.fits(phys, proof, base, l), l, absts(r, phys, proof, base))

def untried.pick(hit: Bool, +c: Cand, rest: List<&2, Cand>) -> List<&2, Cand>:
  match hit:
    case True{}:
      rest
    case False{}:
      c <> rest

def untried(cs: List<&2, Cand>, +tried: List<&2, String>) -> List<&2, Cand>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> r:
      untried.pick(C.mem(tried, cand_key(c)), c, untried(r, tried))

# every rewrite the slow proofs point at, not tried before
def candidates(+hot: List<&2, String>, +phys: String, +proof: String, +base: String, +tried: List<&2, String>) -> List<&2, Cand>:
  +bs = C.blocks(phys)
  +ds = uniq(keep_defs(stmt_defs(hot, C.blocks(proof), C.alias_of(proof)), bs))
  +reach = uniq(List.append(&2, String, ds, callees(ds, bs)))
  untried(List.concat(&2, Cand, [hoists(ds, bs, C.blocks(base)), lifts(reach, bs), pairs(reach, bs, K.records(phys)), onces(hot, phys, proof),
    absts(hot, phys, proof, base)]),
    tried)

# ---- trying one ----

def changed.pick(diff: Bool, +b: String, rest: List<&2, String>) -> List<&2, String>:
  match diff:
    case True{}:
      F.block_name(b) <> rest
    case False{}:
      rest

# the def blocks of the new PROOF.bend that the old one lacks or has otherwise
def changed(+old: List<&2, String>, new: List<&2, String>) -> List<&2, String>:
  match new:
    case Nil{}:
      Nil{}
    case +n <> s:
      changed.pick(Bool.and(F.is_def(n), Bool.not(String.eq(def_block(old, F.block_name(n)), n))), n, changed(old, s))

def sh(+cmd: String) -> IO(Unit):
  do IO<Unit>:
    out : String <- IO.try(String, C.Sys.run(cmd))
    return Unit{}

def q(+s: String) -> String:
  String.concat(["'", s, "'"])

def write_hp(+dir: String, +h: H.HP) -> IO(Bool):
  do IO<Bool>:
    u1 : Unit <- C.write_all(String.append(dir, "/phys.bend"), H.HP.phys(h))
    u2 : Unit <- C.write_all(String.append(dir, "/PROOF.bend"), H.HP.proof(h))
    return True{}

def apply.hoist(ok: Bool, +tdir: String, +h: H.HP) -> IO(String & Bool):
  match ok:
    case True{}:
      do IO<String & Bool>:
        w : Bool <- write_hp(tdir, h)
        return (H.HP.msg(h), True{})
    case False{}:
      IO.pure(String & Bool, (H.HP.msg(h), False{}))

def onces.run(rs: List<&2, String>, +tdir: String, +hot: List<&2, String>, +msgs: String, did: Bool) -> IO(String & Bool):
  match rs:
    case Nil{}:
      IO.pure(String & Bool, (msgs, did))
    case +r <> t:
      do IO<String & Bool>:
        +msg : String <- O.once(tdir, r, hot, 900n)
        onces.run(t, tdir, hot, String.concat([msgs, msg, "\n    "]), Bool.or(did, String.starts_with(msg, "once ")))

# the rewrite on the copy: what it says, and whether it changed anything
def apply(+tdir: String, c: Cand, +par: Nat) -> IO(String & Bool):
  match c:
    case Hoist{+d, +l, +t}:
      do IO<String & Bool>:
        +phys : String <- C.read_all(String.append(tdir, "/phys.bend"))
        +proof : String <- C.read_all(String.append(tdir, "/PROOF.bend"))
        apply.hoist(H.HP.ok(H.hoist.plan(phys, proof, d, l, t)), tdir, H.hoist.plan(phys, proof, d, l, t))
    case LiftC{d}:
      do IO<String & Bool>:
        +msg : String <- L.lift(tdir, d, par, 300n)
        return (msg, String.starts_with(msg, "lifted"))
    case PairC{d}:
      do IO<String & Bool>:
        +msg : String <- P.pair(tdir, d, 900n)
        return (msg, String.starts_with(msg, "paired"))
    case OnceC{rs, hs}:
      onces.run(rs, tdir, hs, SNil{}, False{})
    case AbstC{l}:
      do IO<String & Bool>:
        +msg : String <- B.abst(tdir, [l])
        return (msg, String.starts_with(msg, "abst "))

# nothing new fails, and what was measured got at least 5% faster
def verdict(+ta: List<&2, F.Tm>, +tb: List<&2, F.Tm>) -> Bool:
  Bool.and(Nat.is_eq(fails(tb), 0n), Nat.is_le(Nat.mul(100n, F.total_ms(tb)), Nat.mul(95n, F.total_ms(ta))))

def report(+what: String, +keep: Bool, +ta: List<&2, F.Tm>, +tb: List<&2, F.Tm>) -> String:
  String.concat([Bool.pick(String, keep, "  KEPT    ", "  dropped "), what, ": ", Nat.show(List.length(&2, F.Tm, tb)),
    " proofs measured next to the old ones, ", Nat.show(Nat.div(F.total_ms(ta), 1000n)), "s -> ",
    Nat.show(Nat.div(F.total_ms(tb), 1000n)), "s, ", Nat.show(fails(tb)), " failed"])

def St.times(s: St) -> List<&2, F.Tm>:
  match s:
    case St{t, r, k, g}:
      t

def St.tried(s: St) -> List<&2, String>:
  match s:
    case St{t, r, k, g}:
      r

def St.kept(s: St) -> List<&2, String>:
  match s:
    case St{t, r, k, g}:
      k

def St.gained(s: St) -> Bool:
  match s:
    case St{t, r, k, g}:
      g

def tm_names(ts: List<&2, F.Tm>) -> List<&2, String>:
  match ts:
    case Nil{}:
      Nil{}
    case +t <> r:
      F.Tm.name(t) <> tm_names(r)

def new_tms.pick(seen: Bool, +t: F.Tm, rest: List<&2, F.Tm>) -> List<&2, F.Tm>:
  match seen:
    case True{}:
      rest
    case False{}:
      t <> rest

# the measured proofs the old times do not have
def new_tms(ts: List<&2, F.Tm>, +old: List<&2, String>) -> List<&2, F.Tm>:
  match ts:
    case Nil{}:
      Nil{}
    case +t <> r:
      new_tms.pick(C.mem(old, F.Tm.name(t)), t, new_tms(r, old))

# the times after a rewrite: all of them anew, or the old ones with the new measured
def times_after(all: Bool, +cur: List<&2, F.Tm>, +tb: List<&2, F.Tm>) -> List<&2, F.Tm>:
  match all:
    case True{}:
      tb
    case False{}:
      F.sort_tm(List.append(&2, F.Tm, merge(cur, tb), new_tms(tb, tm_names(cur))))

def measured.keep(keep: Bool, +dir: String, +tdir: String, +key: String, +st: St, +all: Bool, +tb: List<&2, F.Tm>) -> IO(St):
  match keep:
    case True{}:
      do IO<St>:
        u : Unit <- sh(String.concat(["cp ", q(String.append(tdir, "/phys.bend")), " ", q(String.append(tdir, "/PROOF.bend")), " ", q(dir)]))
        return St{times_after(all, St.times(st), tb), key <> St.tried(st), key <> St.kept(st), True{}}
    case False{}:
      IO.pure(St, St{St.times(st), key <> St.tried(st), St.kept(st), St.gained(st)})

def measured(pr: List<&2, F.Tm> & List<&2, F.Tm>, +dir: String, +tdir: String, +key: String, +st: St, +all: Bool, +msg: String) -> IO(St):
  match pr:
    case (+ta, +tb):
      do IO<St>:
        u : Unit <- IO.print(String.concat(["    ", msg]))
        v : Unit <- IO.print(report(key, verdict(ta, tb), ta, tb))
        measured.keep(verdict(ta, tb), dir, tdir, key, st, all, tb)

def calls_any(ts: List<&2, String>, +names: List<&2, String>) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case +t <> r:
      Bool.or(C.mem(names, t), calls_any(r, names))

def callers.pick(hit: Bool, +b: String, rest: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      F.block_name(b) <> rest
    case False{}:
      rest

# the def blocks that name any of these
def callers(bs: List<&2, String>, +names: List<&2, String>) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> r:
      callers.pick(Bool.and(F.is_def(b), calls_any(C.tokens(b), names)), b, callers(r, names))

# what a rewrite touched: the blocks it changed and every block that calls
# them, or every proof when phys.bend changed; old and new are then checked
# side by side, one at a time when they are few (parallel checks on this
# machine's shared cores blur a second or two away)
def applied(did: Bool, +dir: String, +tdir: String, +key: String, +st: St, +old: String, +msg: String, +par: Nat, +cap: Nat) -> IO(St):
  match did:
    case True{}:
      do IO<St>:
        +new : String <- C.read_all(String.append(tdir, "/PROOF.bend"))
        +phys0 : String <- C.read_all(String.append(dir, "/phys.bend"))
        +phys1 : String <- C.read_all(String.append(tdir, "/phys.bend"))
        +ch : List<&2, String> = changed(C.blocks(old), C.blocks(new))
        pr : List<&2, F.Tm> & List<&2, F.Tm> <- F.profile.pair(dir, tdir, uniq(List.append(&2, String, ch, callers(C.blocks(new), ch))),
          Bool.not(String.eq(phys0, phys1)), Bool.pick(Nat, String.eq(phys0, phys1), 1n, par), cap)
        measured(pr, dir, tdir, key, st, Bool.not(String.eq(phys0, phys1)), msg)
    case False{}:
      do IO<St>:
        u : Unit <- IO.print(String.concat(["  skipped ", key, ": ", msg]))
        return St{St.times(st), key <> St.tried(st), St.kept(st), St.gained(st)}

def applied.of(r: String & Bool, +dir: String, +tdir: String, +key: String, +st: St, +old: String, +par: Nat, +cap: Nat) -> IO(St):
  match r:
    case (msg, did):
      applied(did, dir, tdir, key, st, old, msg, par, cap)

def attempt(+dir: String, +c: Cand, +hot: List<&2, String>, +st: St, +par: Nat, +cap: Nat) -> IO(St):
  +tdir = String.append(dir, ".try")
  do IO<St>:
    u : Unit <- sh(String.concat(["rm -rf ", q(tdir), " && cp -r ", q(dir), " ", q(tdir)]))
    +old : String <- C.read_all(String.append(dir, "/PROOF.bend"))
    r : String & Bool <- apply(tdir, c, par)
    applied.of(r, dir, tdir, cand_key(c), st, old, par, cap)

def attempts(cs: List<&2, Cand>, +dir: String, +hot: List<&2, String>, +st: St, +par: Nat, +cap: Nat) -> IO(St):
  match cs:
    case Nil{}:
      IO.pure(St, st)
    case +c <> r:
      do IO<St>:
        +st2 : St <- attempt(dir, c, hot, st, par, cap)
        attempts(r, dir, hot, st2, par, cap)

# ---- the rounds ----

def names_of(cs: List<&2, Cand>) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> r:
      cand_key(c) <> names_of(r)

# one pass over every rewrite the slow proofs point at
def round(+dir: String, +base: String, +st: St, +par: Nat, +cap: Nat) -> IO(St):
  +hot = hot(24n, St.times(st), Nat.mul(3n, median_ms(St.times(st))))
  do IO<St>:
    +phys : String <- C.read_all(String.append(dir, "/phys.bend"))
    +proof : String <- C.read_all(String.append(dir, "/PROOF.bend"))
    +cs : List<&2, Cand> = candidates(hot, phys, proof, base, St.tried(st))
    u : Unit <- IO.print(String.concat(["round: ", Nat.show(List.length(&2, String, hot)), " slow proofs (",
      String.join(hot, ", "), "); ", Nat.show(List.length(&2, Cand, cs)), " rewrites to try: ", String.join(names_of(cs), "; ")]))
    attempts(cs, dir, hot, st, par, cap)

# another round only after one that kept something
def round.if(active: Bool, +dir: String, +base: String, +st: St, +par: Nat, +cap: Nat) -> IO(St):
  match active:
    case True{}:
      round(dir, base, St{St.times(st), St.tried(st), St.kept(st), False{}}, par, cap)
    case False{}:
      IO.pure(St, st)

def rounds(n: Nat, +dir: String, +base: String, +st: St, +par: Nat, +cap: Nat) -> IO(St):
  match n:
    case 0n:
      IO.pure(St, st)
    case 1n+m:
      do IO<St>:
        +st2 : St <- round.if(St.gained(st), dir, base, st, par, cap)
        rounds(m, dir, base, st2, par, cap)

# ---- the whole file, before and after ----

def full_cmd(+d: String) -> String:
  String.concat(["(cd ", q(d), " && ulimit -s 1000000 2>/dev/null; s=$(date +%s); ",
    "o=$(BEND_NO_TELEMETRY=1 BUN_JSC_maxPerThreadStackUsage=805306368 ${BEND:-$HOME/.bend/bin/bend} PROOF.bend 2>&1 | ",
    "grep -e \"All terms\" -e \"^Error\" -e \"^Location\" | head -2 | tr \"\\n\" \" \"); ",
    "echo \"", d, ": $(( $(date +%s) - s ))s: $o\") "])

def tail_of(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      t

def full(+orig: String, +dir: String) -> IO(String):
  do IO<String>:
    out : String <- IO.try(String, C.Sys.run(String.concat([full_cmd(orig), "& ", full_cmd(dir), "& wait"])))
    return String.join(tail_of(String.lines(out)), "\n")

def hot_tms(n: Nat, ts: List<&2, F.Tm>) -> List<&2, F.Tm>:
  match n ts:
    case 0n _:
      Nil{}
    case 1n+m Nil{}:
      Nil{}
    case 1n+m Con{t, r}:
      t <> hot_tms(m, r)

# the search, on <dir> in place; <dir>.orig keeps what it started from
def auto(+dir: String, +par: Nat, +cap: Nat) -> IO(Unit):
  +orig = String.append(dir, ".orig")
  do IO<Unit>:
    u0 : Unit <- sh(String.concat(["rm -rf ", q(orig), " && cp -r ", q(dir), " ", q(orig)]))
    +home : String <- IO.try(String, IO.get_env("HOME"))
    +base : String <- C.read_all(String.append(home, "/.bend/bend2/base.bend"))
    u1 : Unit <- IO.print("profiling every proof...")
    +ts : List<&2, F.Tm> <- F.profile(dir, par, cap)
    u2 : Unit <- IO.print(String.concat([Nat.show(List.length(&2, F.Tm, ts)), " proofs, ", Nat.show(Nat.div(F.total_ms(ts), 1000n)),
      "s in all, ", Nat.show(F.bad_count(ts)), " not ok; slowest:\n", String.join(F.tm_lines(hot_tms(12n, ts)), "\n")]))
    +st : St <- rounds(4n, dir, base, St{ts, Nil{}, Nil{}, True{}}, par, cap)
    u3 : Unit <- IO.print(String.concat(["kept: ", String.join(St.kept(st), "; "), "\nchecking the whole PROOF.bend, before and after..."]))
    +f : String <- full(orig, dir)
    IO.print(f)

# what auto would try for these proofs, without trying it
def cands(+dir: String, +names: List<&2, String>) -> IO(Unit):
  do IO<Unit>:
    +home : String <- IO.try(String, IO.get_env("HOME"))
    +base : String <- C.read_all(String.append(home, "/.bend/bend2/base.bend"))
    +phys : String <- C.read_all(String.append(dir, "/phys.bend"))
    +proof : String <- C.read_all(String.append(dir, "/PROOF.bend"))
    IO.print(String.join(names_of(candidates(names, phys, proof, base, Nil{})), "\n"))
