# Cubo -- proof optimizer, shared by the pair and once rewrites: records,
# identifier substitution, signatures, the cases of a match, and one
# engine that rewrites every call of a name, told what to do by data (a
# closure could only be called once).

import Base
import ./core.bend as C
import ./prof.bend as F

type Kv is Data:
  Kv{k: String, v: String}

type Rec is Data:
  Rec{name: String, fields: List<&2, String>}

type Case is Data:
  Case{pat: String, body: String}

# a hypothesis of a lemma: its position, what it is about (a record), and
# the predicate with that record taken out, as (kb: R) => ...
type Hy is Data:
  Hy{idx: Nat, tgt: String, lam: String}

type Rk is Data:
  PairArgs{k: Nat, g: String, pair: String}
  PinP{k: Nat}
  LemPair{oki: Nat, bi: Nat, g: String, pair: String, hyps: List<&2, Hy>, up: String}
  OnceArgs{hyps: List<&2, Hy>, mine: List<&2, String>, conv: List<&2, String>, lnames: List<&2, String>, up: String}
  Ren{to: String}

# what a rewrite made: whether it applies, why not, both files, and a file
# for the checker proving the new phys defs equal to the old ones
type Plan is Data:
  Plan{ok: Bool, msg: String, phys: String, proof: String, same: String}

def Plan.ok(p: Plan) -> Bool:
  match p:
    case Plan{o, m, a, b, s}:
      o

def Plan.msg(p: Plan) -> String:
  match p:
    case Plan{o, m, a, b, s}:
      m

def Plan.phys(p: Plan) -> String:
  match p:
    case Plan{o, m, a, b, s}:
      a

def Plan.proof(p: Plan) -> String:
  match p:
    case Plan{o, m, a, b, s}:
      b

def Plan.same(p: Plan) -> String:
  match p:
    case Plan{o, m, a, b, s}:
      s

def refuse(+msg: String) -> Plan:
  Plan{False{}, msg, SNil{}, SNil{}, SNil{}}

def Kv.k(x: Kv) -> String:
  match x:
    case Kv{k, v}:
      k

def Kv.v(x: Kv) -> String:
  match x:
    case Kv{k, v}:
      v

def Rec.name(r: Rec) -> String:
  match r:
    case Rec{n, f}:
      n

def Rec.fields(r: Rec) -> List<&2, String>:
  match r:
    case Rec{n, f}:
      f

def Case.pat(c: Case) -> String:
  match c:
    case Case{p, b}:
      p

def Case.body(c: Case) -> String:
  match c:
    case Case{p, b}:
      b

def Hy.idx(h: Hy) -> Nat:
  match h:
    case Hy{i, t, l}:
      i

def Hy.tgt(h: Hy) -> String:
  match h:
    case Hy{i, t, l}:
      t

def Hy.lam(h: Hy) -> String:
  match h:
    case Hy{i, t, l}:
      l

# ---- small things ----

def ptype(+chunk: String) -> String:
  String.trim(String.drop(chunk, Nat.add(1n, C.or_len(C.find(chunk, ":"), String.length(chunk)))))

def ws_of(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+h, +t}:
      Bool.pick(String, Char.is_space(h), SCon{h, ws_of(t)}, SNil{})

def ltake(+xs: List<&2, String>, n: Nat) -> List<&2, String>:
  List.take(&2, String, xs, n)

def ldrop(+xs: List<&2, String>, n: Nat) -> List<&2, String>:
  List.drop(&2, String, xs, n)

def trims(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      String.trim(h) <> trims(t)

def lookup(env: List<&2, Kv>, +w: String) -> Maybe<&2, String>:
  match env:
    case Nil{}:
      None{}
    case +e <> r:
      Bool.pick(Maybe<&2, String>, String.eq(Kv.k(e), w), Some{Kv.v(e)}, lookup(r, w))

def indent_by(ls: List<&2, String>, +pre: String) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> r:
      Bool.pick(String, String.is_empty(String.trim(l)), l, String.append(pre, l)) <> indent_by(r, pre)

def indent(+text: String, n: Nat) -> String:
  String.join(indent_by(String.lines(text), String.repeat(" ", n)), "\n")

# the text of name(a, b, ...) with each argument trimmed
def call_text(+name: String, +args: List<&2, String>) -> String:
  String.concat([name, "(", String.join(trims(args), ", "), ")"])

# for a whole call g(...), what lies inside its parens
def inner(+a: String, +g: String) -> String:
  String.take(String.drop(a, Nat.add(1n, String.length(g))), Nat.sub(String.length(a), Nat.add(2n, String.length(g))))

def first_arg(+a: String, +g: String) -> String:
  String.trim(C.first_of(C.split_top(inner(a, g), ',')))

def is_call_of(+a: String, +g: String) -> Bool:
  Bool.and(String.starts_with(a, String.append(g, "(")), String.ends_with(a, ")"))

# ---- identifiers ----

def word_char(+c: Char) -> Bool:
  C.is_ident(c)

def take_word(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+h, t}:
      Bool.pick(String, word_char(h), SCon{h, take_word(t)}, SNil{})

def next_is(+s: String, +c: Char) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{h, t}:
      Char.is_eq(h, c)

# a bare name: no dot in it, not called, not a constructor
def sub_word(+w: String, +rest: String, +env: List<&2, Kv>) -> String:
  Bool.pick(String, Bool.or(String.contains(w, "."), Bool.or(next_is(rest, '('), next_is(rest, '{'))), w,
    Maybe.default(&2, String, lookup(env, w), w))

def head_word(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{h, t}:
      word_char(h)

def sv.go(fuel: Nat, isw: Bool, +s: String, +env: List<&2, Kv>) -> String:
  match fuel isw:
    case 0n _:
      s
    case 1n+f True{}:
      String.append(sub_word(take_word(s), String.drop(s, String.length(take_word(s))), env),
        sv.go(f, head_word(String.drop(s, String.length(take_word(s)))), String.drop(s, String.length(take_word(s))), env))
    case 1n+f False{}:
      match s:
        case SNil{}:
          SNil{}
        case SCon{+h, +t}:
          SCon{h, sv.go(f, head_word(t), t, env)}

# every bare name in env replaced by its value
def subst_vars(+s: String, +env: List<&2, Kv>) -> String:
  sv.go(1n+String.length(s), head_word(s), s, env)

# ---- records and signatures ----

def rec_of.go(+b: String, +name: String, +line: String) -> Rec:
  Rec{name, C.names(C.split_top(String.take(String.drop(line, Nat.add(1n, String.length(name))),
    Nat.sub(String.length(line), Nat.add(2n, String.length(name)))), ','))}

def ctor_lines.pick(hit: Bool, +l: String, rest: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      String.trim(l) <> rest
    case False{}:
      rest

def ctor_lines(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> r:
      ctor_lines.pick(Bool.and(String.starts_with(l, "  "), String.ends_with(String.trim_end(l), "}")), l, ctor_lines(r))

def rec.pick(one: Bool, +b: String, +name: String, +cs: List<&2, String>, rest: List<&2, Rec>) -> List<&2, Rec>:
  match one:
    case True{}:
      rec_of.go(b, name, C.first_of(cs)) <> rest
    case False{}:
      rest

def type_name(+b: String) -> String:
  C.first_of(String.split(String.drop(b, 5n), ' '))

# the types of phys.bend that are one constructor on one line: R{f: T, ...}
def records.go(bs: List<&2, String>) -> List<&2, Rec>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> r:
      rec.pick(Bool.and(String.starts_with(b, "type "),
        Bool.and(Nat.is_eq(List.length(&2, String, ctor_lines(String.lines(b))), 1n),
          String.starts_with(C.first_of(ctor_lines(String.lines(b))), String.append(type_name(b), "{")))),
        b, type_name(b), ctor_lines(String.lines(b)), records.go(r))

def records(+phys: String) -> List<&2, Rec>:
  records.go(C.blocks(phys))

def fields_of(rs: List<&2, Rec>, +name: String) -> List<&2, String>:
  match rs:
    case Nil{}:
      Nil{}
    case +r <> t:
      Bool.pick(List<&2, String>, String.eq(Rec.name(r), name), Rec.fields(r), fields_of(t, name))

def is_rec(+rs: List<&2, Rec>, +name: String) -> Bool:
  Nat.is_le(1n, List.length(&2, String, fields_of(rs, name)))

# the pattern that opens a record once, and the record rebuilt from it
def fpat(n: Nat, +i: Nat) -> List<&2, String>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      String.append("+u", Nat.show(i)) <> fpat(m, 1n+i)

def frec(n: Nat, +i: Nat) -> List<&2, String>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      String.append("u", Nat.show(i)) <> frec(m, 1n+i)

def open_pat(+r: String, n: Nat) -> String:
  String.concat([r, "{", String.join(fpat(n, 1n), ", "), "}"])

def rebuilt(+r: String, n: Nat) -> String:
  String.concat([r, "{", String.join(frec(n, 1n), ", "), "}"])

def with_params(+sig: String, +ps: List<&2, String>) -> String:
  C.sig_text(C.Sig{C.Sig.pre(C.sig_of(sig)), ps, C.Sig.post(C.sig_of(sig))})

def set_concl.go(+sig: String, m: Maybe<&2, Nat>, +new: String) -> String:
  match m:
    case None{}:
      sig
    case Some{i}:
      String.concat([String.take(sig, Nat.add(2n, i)), " ", new, ":"])

def set_conclusion(+sig: String, +new: String) -> String:
  set_concl.go(sig, F.arrow_idx(sig), new)

def conclusion(+b: String) -> String:
  F.ret_type(b)

def body_of(+b: String) -> String:
  String.drop(b, C.sig_len(b, 0n))

# ---- the cases of a match ----

def is_case_at(+l: String, +pre: String) -> Bool:
  Bool.and(String.starts_with(l, String.append(pre, "case ")), String.ends_with(String.trim_end(l), ":"))

type Cs2 is Data:
  Cs2{pending: List<&2, String>, cases: List<&2, Case>}

def cs2.line(isc: Bool, +l: String, +depth: Nat, p: List<&2, String>, cs: List<&2, Case>) -> Cs2:
  match isc:
    case True{}:
      Cs2{Nil{}, Case{String.trim(F.drop_colon(String.trim(String.drop(String.trim(l), 5n)))), String.join(p, "\n")} <> cs}
    case False{}:
      Cs2{String.drop(l, Nat.add(2n, depth)) <> p, cs}

def cs2.push(+l: String, +depth: Nat, acc: Cs2) -> Cs2:
  match acc:
    case Cs2{p, cs}:
      cs2.line(is_case_at(l, String.repeat(" ", depth)), l, depth, p, cs)

def cs2.go(ls: List<&2, String>, +depth: Nat) -> Cs2:
  match ls:
    case Nil{}:
      Cs2{Nil{}, Nil{}}
    case +l <> r:
      cs2.push(l, depth, cs2.go(r, depth))

def cs2.fin(acc: Cs2) -> List<&2, Case>:
  match acc:
    case Cs2{p, cs}:
      cs

# the cases of a match written at depth, each body taken out of its indent
def cases_at(ls: List<&2, String>, +depth: Nat) -> List<&2, Case>:
  cs2.fin(cs2.go(ls, depth))

def first_code(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      SNil{}
    case +l <> r:
      Bool.pick(String, String.is_empty(String.trim(l)), first_code(r), l)

def after_line(ls: List<&2, String>, +target: String) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> +r:
      Bool.pick(List<&2, String>, String.eq(String.trim(l), target), r, after_line(r, target))

# ---- every call of a name, rewritten as its kind says ----

def pa.pick(hit: Bool, +args: List<&2, String>, +k: Nat, +a: String, +g: String, +pair: String) -> Maybe<&2, List<&2, String>>:
  match hit:
    case True{}:
      Some{List.append(&2, String, ltake(args, k),
        String.append(" ", call_text(pair, C.split_top(inner(a, g), ','))) <> ldrop(args, Nat.add(2n, k)))}
    case False{}:
      None{}

# (g(X, e..), X) at k, k+1 becomes pair(X, e..)
def pair_args(+args: List<&2, String>, +k: Nat, +g: String, +pair: String) -> Maybe<&2, List<&2, String>>:
  pa.pick(Bool.and(is_call_of(String.trim(C.nth(args, k)), g),
    String.eq(String.trim(C.nth(args, 1n+k)), first_arg(String.trim(C.nth(args, k)), g))),
    args, k, String.trim(C.nth(args, k)), g, pair)

def hy_at(hs: List<&2, Hy>, +i: Nat) -> Maybe<&2, Hy>:
  match hs:
    case Nil{}:
      None{}
    case +h <> r:
      Bool.pick(Maybe<&2, Hy>, Nat.is_eq(Hy.idx(h), i), Some{h}, hy_at(r, i))

def lp.arg(m: Maybe<&2, Hy>, +a: String, +xe: String, +up: String) -> String:
  match m:
    case None{}:
      a
    case Some{h}:
      String.concat([" ", up, "(", Hy.lam(h), ", ", xe, ", ", String.trim(a), ")"])

def lp.one(isok: Bool, isb: Bool, +a: String, rest: List<&2, String>, +hyps: List<&2, Hy>, +i: Nat, +pcall: String,
  +xe: String, +up: String) -> List<&2, String>:
  match isok isb:
    case True{} _:
      String.append(" ", pcall) <> rest
    case False{} True{}:
      rest
    case False{} False{}:
      lp.arg(hy_at(hyps, i), a, xe, up) <> rest

def lp.go(args: List<&2, String>, +i: Nat, +oki: Nat, +bi: Nat, +hyps: List<&2, Hy>, +pcall: String, +xe: String, +up: String)
  -> List<&2, String>:
  match args:
    case Nil{}:
      Nil{}
    case +a <> r:
      lp.one(Nat.is_eq(i, oki), Nat.is_eq(i, bi), a, lp.go(r, 1n+i, oki, bi, hyps, pcall, xe, up), hyps, i, pcall, xe, up)

def lp.pick(hit: Bool, +args: List<&2, String>, +oki: Nat, +bi: Nat, +g: String, +pair: String, +hyps: List<&2, Hy>,
  +up: String) -> Maybe<&2, List<&2, String>>:
  match hit:
    case True{}:
      Some{lp.go(args, 0n, oki, bi, hyps, call_text(pair, C.split_top(inner(String.trim(C.nth(args, oki)), g), ',')),
        String.join(trims(C.split_top(inner(String.trim(C.nth(args, oki)), g), ',')), ", "), up)}
    case False{}:
      None{}

# a lemma about the paired def: its (ok, b) become the pair, and each
# hypothesis about b is carried over by up
def lem_pair(+args: List<&2, String>, +oki: Nat, +bi: Nat, +g: String, +pair: String, +hyps: List<&2, Hy>, +up: String)
  -> Maybe<&2, List<&2, String>>:
  lp.pick(Bool.and(is_call_of(String.trim(C.nth(args, oki)), g),
    String.eq(String.trim(C.nth(args, bi)), first_arg(String.trim(C.nth(args, oki)), g))), args, oki, bi, g, pair, hyps, up)

def mk_env(ns: List<&2, String>, +args: List<&2, String>, +i: Nat) -> List<&2, Kv>:
  match ns:
    case Nil{}:
      Nil{}
    case +n <> r:
      Kv{n, String.concat(["(", String.trim(C.nth(args, i)), ")"])} <> mk_env(r, args, 1n+i)

def starts_any(cs: List<&2, String>, +a: String) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case +c <> r:
      Bool.or(String.starts_with(a, String.append(c, "(")), starts_any(r, a))

def oa.arg(m: Maybe<&2, Hy>, +a: String, +mine: List<&2, String>, +conv: List<&2, String>, +env: List<&2, Kv>, +up: String) -> String:
  match m:
    case None{}:
      a
    case Some{+h}:
      Bool.pick(String, Bool.or(C.mem(mine, String.trim(a)), starts_any(conv, String.trim(a))), a,
        String.concat([" ", up, "(", subst_vars(Hy.lam(h), env), ", ", subst_vars(Hy.tgt(h), env), ", ", String.trim(a), ")"]))

def oa.go(args: List<&2, String>, +i: Nat, +hyps: List<&2, Hy>, +mine: List<&2, String>, +conv: List<&2, String>,
  +env: List<&2, Kv>, +up: String) -> List<&2, String>:
  match args:
    case Nil{}:
      Nil{}
    case +a <> r:
      oa.arg(hy_at(hyps, i), a, mine, conv, env, up) <> oa.go(r, 1n+i, hyps, mine, conv, env, up)

def apply(k: Rk, +args: List<&2, String>) -> Maybe<&2, List<&2, String>>:
  match k:
    case PairArgs{+i, g, pair}:
      pair_args(args, i, g, pair)
    case PinP{+i}:
      Some{List.append(&2, String, ltake(args, i), " p" <> ldrop(args, Nat.add(2n, i)))}
    case LemPair{oki, bi, g, pair, hyps, up}:
      lem_pair(args, oki, bi, g, pair, hyps, up)
    case OnceArgs{hyps, mine, conv, lnames, up}:
      Some{oa.go(args, 0n, hyps, mine, conv, mk_env(lnames, args, 0n), up)}
    case Ren{to}:
      Some{args}

def out_name(k: Rk, +name: String) -> String:
  match k:
    case Ren{to}:
      to
    case PairArgs{i, g, pair}:
      name
    case PinP{i}:
      name
    case LemPair{oki, bi, g, pair, hyps, up}:
      name
    case OnceArgs{hyps, mine, conv, lnames, up}:
      name

def call_at(+s: String, +pat: String, +prev: Char) -> Bool:
  Bool.and(String.starts_with(s, pat), Bool.not(C.is_ident(prev)))

def rc.after(+s: String, +pat: String) -> String:
  String.drop(s, String.length(pat))

def rc.close(+s: String, +pat: String) -> Nat:
  C.close_idx(rc.after(s, pat), 0n)

def rc.tail(+s: String, +pat: String) -> String:
  String.drop(rc.after(s, pat), 1n+rc.close(s, pat))

def rc.emit(m: Maybe<&2, List<&2, String>>, +orig: String, +name: String) -> String:
  match m:
    case None{}:
      orig
    case Some{a}:
      String.concat([name, "(", String.join(a, ","), ")"])

def rc.call(+s: String, +pat: String, +name: String, +k: Rk) -> String:
  rc.emit(apply(k, C.split_top(String.take(rc.after(s, pat), rc.close(s, pat)), ',')),
    String.take(s, Nat.add(String.length(pat), 1n+rc.close(s, pat))), out_name(k, name))

def rc(fuel: Nat, here: Bool, +s: String, +pat: String, +name: String, +k: Rk) -> String:
  match fuel here:
    case 0n _:
      s
    case 1n+f True{}:
      String.append(rc.call(s, pat, name, k), rc(f, call_at(rc.tail(s, pat), pat, ')'), rc.tail(s, pat), pat, name, k))
    case 1n+f False{}:
      match s:
        case SNil{}:
          SNil{}
        case SCon{+h, +t}:
          SCon{h, rc(f, call_at(t, pat, h), t, pat, name, k)}

def rewrite_calls.if(hit: Bool, +text: String, +name: String, +k: Rk) -> String:
  match hit:
    case True{}:
      rc(1n+String.length(text), call_at(text, String.append(name, "("), ' '), text, String.append(name, "("), name, k)
    case False{}:
      text

# every call name(...) in text, rewritten as k says
def rewrite_calls(+text: String, +name: String, +k: Rk) -> String:
  rewrite_calls.if(String.contains(text, String.append(name, "(")), text, name, k)

# the arguments of the first call name(...) in text
def first_args.go(m: Maybe<&2, Nat>, +text: String, +name: String) -> List<&2, String>:
  match m:
    case None{}:
      Nil{}
    case Some{+i}:
      C.split_top(String.take(String.drop(text, Nat.add(i, 1n+String.length(name))),
        C.close_idx(String.drop(text, Nat.add(i, 1n+String.length(name))), 0n)), ',')

def first_args(+text: String, +name: String) -> List<&2, String>:
  first_args.go(C.find(text, String.append(name, "(")), text, name)
