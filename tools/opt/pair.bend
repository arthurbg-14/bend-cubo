# Cubo -- proof optimizer, the pair rewrite.
#
# A recursive phys def D(n, ok, b, ...) whose every call passes ok = G(X, e..)
# and b = X: the checker, which shares nothing, carries X twice into each
# step. D gets the pair (X, G(X, e..)) instead, made by D.pair, which opens X
# once. The lemmas about D take the pair too, their hypotheses about b ask
# it of the pair's body, and each call carries its hypothesis over with
# D.pair_up. D.same, for the checker, proves the new D equal to the old
# one for every n.

import Base
import ./core.bend as C
import ./prof.bend as F
import ./calls.bend as K
import ./lift.bend as L

type Pd is Data:
  Pd{ok: Bool, why: String, k: Nat, rec: String, g: String, eargs: List<&2, String>}

def Pd.ok(p: Pd) -> Bool:
  match p:
    case Pd{o, w, k, r, g, e}:
      o

def Pd.why(p: Pd) -> String:
  match p:
    case Pd{o, w, k, r, g, e}:
      w

def Pd.k(p: Pd) -> Nat:
  match p:
    case Pd{o, w, k, r, g, e}:
      k

def Pd.rec(p: Pd) -> String:
  match p:
    case Pd{o, w, k, r, g, e}:
      r

def Pd.g(p: Pd) -> String:
  match p:
    case Pd{o, w, k, r, g, e}:
      g

def Pd.eargs(p: Pd) -> List<&2, String>:
  match p:
    case Pd{o, w, k, r, g, e}:
      e

def pd.no(+why: String) -> Pd:
  Pd{False{}, why, 0n, SNil{}, SNil{}, Nil{}}

# ---- finding the pair ----

def head_call(+a: String) -> String:
  String.trim(C.take_until_paren(a))

# at i: a Bool and then a record, and the self call passes g(X, ..) and X there
def pair_here(+ps: List<&2, String>, +recs: List<&2, K.Rec>, +args: List<&2, String>, +i: Nat) -> Bool:
  Bool.and(String.eq(K.ptype(C.nth(ps, i)), "Bool"),
    Bool.and(K.is_rec(recs, K.ptype(C.nth(ps, 1n+i))),
      Bool.and(String.ends_with(String.trim(C.nth(args, i)), ")"),
        String.eq(String.trim(C.nth(args, 1n+i)), K.first_arg(String.trim(C.nth(args, i)), head_call(String.trim(C.nth(args, i))))))))

def find_k.pick(hit: Bool, +i: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{i}
    case False{}:
      rest

def find_k(n: Nat, +ps: List<&2, String>, +recs: List<&2, K.Rec>, +args: List<&2, String>, +i: Nat) -> Maybe<&2, Nat>:
  match n:
    case 0n:
      None{}
    case 1n+m:
      find_k.pick(pair_here(ps, recs, args, i), i, find_k(m, ps, recs, args, 1n+i))

def all_params(es: List<&2, String>, +names: List<&2, String>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case +e <> r:
      Bool.and(C.mem(names, e), all_params(r, names))

def pd.found(+k: Nat, +ps: List<&2, String>, +args: List<&2, String>) -> Pd:
  +a = String.trim(C.nth(args, k))
  +g = head_call(a)
  +es = K.ldrop(K.trims(C.split_top(K.inner(a, g), ',')), 1n)
  Bool.pick(Pd, all_params(es, C.names(ps)), Pd{True{}, SNil{}, k, K.ptype(C.nth(ps, 1n+k)), g, es},
    pd.no(String.concat(["the decision ", a, " takes more than parameters"])))

def pd.of(m: Maybe<&2, Nat>, +ps: List<&2, String>, +args: List<&2, String>) -> Pd:
  match m:
    case None{}:
      pd.no("no (Bool, record) pair that every call fills with g(X, ..) and X")
    case Some{k}:
      pd.found(k, ps, args)

def pd.read(+b: String, +d: String, +recs: List<&2, K.Rec>) -> Pd:
  +ps = C.Sig.ps(C.sig_of(b))
  +args = K.first_args(K.body_of(b), d)
  pd.of(find_k(List.length(&2, String, ps), ps, recs, args, 0n), ps, args)

# ---- the body over (n, ok), rebuilt over n, then the pair, then ok ----

def pat_n(+p: String) -> String:
  C.first_of(String.split(String.trim(p), ' '))

def pat_ok(+p: String) -> String:
  String.trim(String.drop(String.trim(p), String.length(pat_n(p))))

def n_fits(+np: String, +ncls: String) -> Bool:
  Bool.or(String.eq(np, "_"), Bool.or(String.eq(np, ncls), Bool.and(Bool.not(String.eq(ncls, "0n")), String.starts_with(np, "1n+"))))

def ok_fits(+op: String, +okv: String) -> Bool:
  Bool.or(String.eq(op, "_"), String.eq(op, String.append(okv, "{}")))

def pick_case(cs: List<&2, K.Case>, +ncls: String, +okv: String) -> String:
  match cs:
    case Nil{}:
      SNil{}
    case +c <> r:
      Bool.pick(String, Bool.and(n_fits(pat_n(K.Case.pat(c)), ncls), ok_fits(pat_ok(K.Case.pat(c)), okv)),
        K.Case.body(c), pick_case(r, ncls, okv))

def succ_pat(cs: List<&2, K.Case>) -> String:
  match cs:
    case Nil{}:
      "1n+m"
    case +c <> r:
      Bool.pick(String, String.starts_with(pat_n(K.Case.pat(c)), "1n+"), pat_n(K.Case.pat(c)), succ_pat(r))

def arm.ok(same: Bool, +bt: String, +bf: String, +okn: String, +d: Nat) -> String:
  match same:
    case True{}:
      K.indent(bt, d)
    case False{}:
      String.concat([String.repeat(" ", d), "match ", okn, ":\n", String.repeat(" ", Nat.add(2n, d)), "case True{}:\n",
        K.indent(bt, Nat.add(4n, d)), "\n", String.repeat(" ", Nat.add(2n, d)), "case False{}:\n", K.indent(bf, Nat.add(4n, d))])

def arm(+cs: List<&2, K.Case>, +ncls: String, +pn: String, +bn: String, +okn: String) -> String:
  String.concat(["    case ", ncls, ":\n      match ", pn, ":\n        case (", bn, ", ", okn, "):\n",
    arm.ok(String.eq(String.trim(pick_case(cs, ncls, "True")), String.trim(pick_case(cs, ncls, "False"))),
      pick_case(cs, ncls, "True"), pick_case(cs, ncls, "False"), okn, 10n)])

def nat_bool_body(+cs: List<&2, K.Case>, +nn: String, +bn: String, +okn: String) -> String:
  String.concat(["\n  match ", nn, ":\n", arm(cs, "0n", "p", bn, okn), "\n", arm(cs, succ_pat(cs), "p", bn, okn)])

def rewrite_cases(cs: List<&2, K.Case>, +name: String, +k: K.Rk) -> List<&2, K.Case>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> r:
      K.Case{K.Case.pat(c), K.rewrite_calls(K.Case.body(c), name, k)} <> rewrite_cases(r, name, k)

def cases_of_match(+b: String, +first: String) -> List<&2, K.Case>:
  K.cases_at(K.after_line(String.lines(K.body_of(b)), String.trim(first)), 4n)

# ---- phys.bend ----

def pair_def(+d: String, +bn: String, +r: String, +nf: Nat, +g: String, +echunks: List<&2, String>, +es: List<&2, String>) -> String:
  String.concat(["def ", d, ".pair(", bn, ": ", r, ", ", String.join(K.trims(echunks), ", "), ") -> ", r, " & Bool:\n",
    "  match ", bn, ":\n    case ", K.open_pat(r, nf), ":\n      (", K.rebuilt(r, nf), ", ",
    K.call_text(g, K.rebuilt(r, nf) <> es), ")\n"])

def chunks_of(es: List<&2, String>, +ps: List<&2, String>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> r:
      C.nth(ps, C.index_of(C.names(ps), e)) <> chunks_of(r, ps)

def new_ps(+ps: List<&2, String>, +k: Nat, +r: String) -> List<&2, String>:
  List.append(&2, String, K.ltake(ps, k),
    String.concat([K.ws_of(C.nth(ps, k)), "p: ", r, " & Bool"]) <> K.ldrop(ps, Nat.add(2n, k)))

def phys_blocks(bs: List<&2, String>, +d: String, +newd: String, +k: K.Rk) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> r:
      Bool.pick(String, String.starts_with(b, String.concat(["def ", d, "("])), newd, K.rewrite_calls(b, d, k))
        <> phys_blocks(r, d, newd, k)

def new_def(+b: String, +d: String, +p: Pd, +recs: List<&2, K.Rec>) -> String:
  +ps = C.Sig.ps(C.sig_of(b))
  +names = C.names(ps)
  +first = String.trim(K.first_code(String.lines(K.body_of(b))))
  String.concat([pair_def(d, C.nth(names, 1n+Pd.k(p)), Pd.rec(p), List.length(&2, String, K.fields_of(recs, Pd.rec(p))), Pd.g(p),
      chunks_of(Pd.eargs(p), ps), Pd.eargs(p)), "\n",
    K.with_params(C.sig_part(b), new_ps(ps, Pd.k(p), Pd.rec(p))),
    nat_bool_body(rewrite_cases(cases_of_match(b, first), d, K.PairArgs{Pd.k(p), Pd.g(p), String.append(d, ".pair")}),
      C.nth(names, 0n), C.nth(names, 1n+Pd.k(p)), C.nth(names, Pd.k(p)))])

# ---- PROOF.bend ----

type Ab is Data:
  Ab{name: String, oki: Nat, bi: Nat, hyps: List<&2, K.Hy>}

def Ab.name(a: Ab) -> String:
  match a:
    case Ab{n, o, b, h}:
      n

def Ab.oki(a: Ab) -> Nat:
  match a:
    case Ab{n, o, b, h}:
      o

def Ab.bi(a: Ab) -> Nat:
  match a:
    case Ab{n, o, b, h}:
      b

def Ab.hyps(a: Ab) -> List<&2, K.Hy>:
  match a:
    case Ab{n, o, b, h}:
      h

def mentions(+t: String, +v: String) -> Bool:
  Bool.not(String.eq(K.subst_vars(t, [K.Kv{v, "kb_seen_"}]), t))

def hyps.pick(hit: Bool, +p: String, +i: Nat, +bn: String, +qr: String, rest: List<&2, K.Hy>) -> List<&2, K.Hy>:
  match hit:
    case True{}:
      K.Hy{i, bn, String.concat(["(kb: ", qr, ") => ", K.subst_vars(K.ptype(p), [K.Kv{bn, "kb"}])])} <> rest
    case False{}:
      rest

def hyps.go(ps: List<&2, String>, +i: Nat, +oki: Nat, +bi: Nat, +bn: String, +qr: String) -> List<&2, K.Hy>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> r:
      hyps.pick(Bool.and(Bool.not(Bool.or(Nat.is_eq(i, oki), Nat.is_eq(i, bi))), mentions(K.ptype(p), bn)), p, i, bn, qr,
        hyps.go(r, 1n+i, oki, bi, bn, qr))

def about.of(+b: String, +args: List<&2, String>, +k: Nat, +qr: String) -> Maybe<&2, Ab>:
  +names = C.names(C.Sig.ps(C.sig_of(b)))
  +okl = String.trim(C.nth(args, k))
  +bl = String.trim(C.nth(args, 1n+k))
  Bool.pick(Maybe<&2, Ab>, Bool.and(Bool.and(C.mem(names, okl), C.mem(names, bl)), Bool.not(String.eq(okl, bl))),
    Some{Ab{F.block_name(b), C.index_of(names, okl), C.index_of(names, bl),
      hyps.go(C.Sig.ps(C.sig_of(b)), 0n, C.index_of(names, okl), C.index_of(names, bl), bl, qr)}},
    None{})

def about.pick(m: Maybe<&2, Ab>, rest: List<&2, Ab>) -> List<&2, Ab>:
  match m:
    case None{}:
      rest
    case Some{a}:
      a <> rest

# the lemmas whose statement is about D(.., ok, b, ..) for parameters ok and b
def abouts(bs: List<&2, String>, +qd: String, +k: Nat, +qr: String) -> List<&2, Ab>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> r:
      about.pick(Bool.pick(Maybe<&2, Ab>, Bool.and(F.is_def(b), String.contains(C.sig_part(b), String.append(qd, "("))),
        about.of(b, K.first_args(C.sig_part(b), qd), k, qr), None{}), abouts(r, qd, k, qr))

def find_ab(abs: List<&2, Ab>, +n: String) -> Maybe<&2, Ab>:
  match abs:
    case Nil{}:
      None{}
    case +a <> r:
      Bool.pick(Maybe<&2, Ab>, String.eq(Ab.name(a), n), Some{a}, find_ab(r, n))

def lemma_calls(abs: List<&2, Ab>, +text: String, +qg: String, +qpair: String, +up: String) -> String:
  match abs:
    case Nil{}:
      text
    case +a <> r:
      lemma_calls(r, K.rewrite_calls(text, Ab.name(a), K.LemPair{Ab.oki(a), Ab.bi(a), qg, qpair, Ab.hyps(a), up}), qg, qpair, up)

def ab_ps.one(isok: Bool, isb: Bool, +p: String, +bn: String, +qr: String, +ofp: String, rest: List<&2, String>) -> List<&2, String>:
  match isok isb:
    case True{} _:
      String.concat([K.ws_of(p), "p: ", qr, " & Bool"]) <> rest
    case False{} True{}:
      rest
    case False{} False{}:
      K.subst_vars(p, [K.Kv{bn, String.append(ofp, "(p)")}]) <> rest

def ab_ps.go(ps: List<&2, String>, +i: Nat, +a: Ab, +bn: String, +qr: String, +ofp: String) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> r:
      ab_ps.one(Nat.is_eq(i, Ab.oki(a)), Nat.is_eq(i, Ab.bi(a)), p, bn, qr, ofp, ab_ps.go(r, 1n+i, a, bn, qr, ofp))

type Cx is Data:
  Cx{k: Nat, qd: String, qg: String, qpair: String, qr: String, ofp: String, up: String, abs: List<&2, Ab>}

def Cx.k(c: Cx) -> Nat:
  match c:
    case Cx{k, qd, qg, qp, qr, ofp, up, abs}:
      k

def Cx.qd(c: Cx) -> String:
  match c:
    case Cx{k, qd, qg, qp, qr, ofp, up, abs}:
      qd

def Cx.qr(c: Cx) -> String:
  match c:
    case Cx{k, qd, qg, qp, qr, ofp, up, abs}:
      qr

def Cx.ofp(c: Cx) -> String:
  match c:
    case Cx{k, qd, qg, qp, qr, ofp, up, abs}:
      ofp

def Cx.qg(c: Cx) -> String:
  match c:
    case Cx{k, qd, qg, qp, qr, ofp, up, abs}:
      qg

def Cx.qpair(c: Cx) -> String:
  match c:
    case Cx{k, qd, qg, qp, qr, ofp, up, abs}:
      qp

def Cx.up(c: Cx) -> String:
  match c:
    case Cx{k, qd, qg, qp, qr, ofp, up, abs}:
      up

def Cx.abs(c: Cx) -> List<&2, Ab>:
  match c:
    case Cx{k, qd, qg, qp, qr, ofp, up, abs}:
      abs

def rw_text(+t: String, +cx: Cx) -> String:
  lemma_calls(Cx.abs(cx), K.rewrite_calls(t, Cx.qd(cx), K.PairArgs{Cx.k(cx), Cx.qg(cx), Cx.qpair(cx)}), Cx.qg(cx), Cx.qpair(cx), Cx.up(cx))

def ab_cases(cs: List<&2, K.Case>, +cx: Cx) -> List<&2, K.Case>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> r:
      K.Case{K.Case.pat(c), rw_text(K.Case.body(c), cx)} <> ab_cases(r, cx)

# a lemma about D, over the pair
def ab_block(+b: String, +a: Ab, +cx: Cx) -> String:
  +ps = C.Sig.ps(C.sig_of(b))
  +names = C.names(ps)
  +bn = C.nth(names, Ab.bi(a))
  +first = String.trim(K.first_code(String.lines(K.body_of(b))))
  String.append(
    K.rewrite_calls(K.with_params(C.sig_part(b), ab_ps.go(ps, 0n, a, bn, Cx.qr(cx), Cx.ofp(cx))), Cx.qd(cx), K.PinP{Cx.k(cx)}),
    nat_bool_body(ab_cases(cases_of_match(b, first), cx), C.nth(names, 0n), bn, C.nth(names, Ab.oki(a))))

def proof_block.of(m: Maybe<&2, Ab>, +b: String, +cx: Cx) -> String:
  match m:
    case None{}:
      rw_text(b, cx)
    case Some{a}:
      ab_block(b, a, cx)

def proof_blocks(bs: List<&2, String>, +cx: Cx) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> r:
      Bool.pick(String, F.is_def(b), proof_block.of(find_ab(Cx.abs(cx), F.block_name(b)), b, cx), b) <> proof_blocks(r, cx)

def qenv(ts: List<&2, String>, +al: String) -> List<&2, K.Kv>:
  match ts:
    case Nil{}:
      Nil{}
    case +t <> r:
      K.Kv{t, String.concat([al, ".", t])} <> qenv(r, al)

def qualify_one(+t: String, +al: String, +types: List<&2, String>) -> String:
  K.subst_vars(t, qenv(types, al))

def qualify_all(cs: List<&2, String>, +al: String, +types: List<&2, String>) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> r:
      String.concat([String.trim(C.first_of(String.split(c, ':'))), ": ", qualify_one(K.ptype(c), al, types)]) <> qualify_all(r, al, types)

def helpers(+cx: Cx, +d: String, +es: List<&2, String>, +echunks: List<&2, String>, +nf: Nat, +al: String, +types: List<&2, String>) -> String:
  String.concat(["def ", Cx.ofp(cx), "(p: ", Cx.qr(cx), " & Bool) -> ", Cx.qr(cx), ":\n  match p:\n    case (b, o):\n      b\n\n",
    "def ", Cx.up(cx), "(-k: ", Cx.qr(cx), " -> Type, c: ", Cx.qr(cx), ", ", String.join(qualify_all(echunks, al, types), ", "),
    ", h: k(c)) -> k(", Cx.ofp(cx), "(", K.call_text(Cx.qpair(cx), "c" <> es), ")):\n  match c:\n    case ",
    al, ".", K.open_pat(String.drop(Cx.qr(cx), Nat.add(1n, String.length(al))), nf), ":\n      h\n"])

def type_names.pick(hit: Bool, +b: String, rest: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      K.type_name(b) <> rest
    case False{}:
      rest

def type_names(bs: List<&2, String>) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> r:
      type_names.pick(String.starts_with(b, "type "), b, type_names(r))

def ab_names(abs: List<&2, Ab>) -> List<&2, String>:
  match abs:
    case Nil{}:
      Nil{}
    case +a <> r:
      Ab.name(a) <> ab_names(r)

# the line the first def starts at
# the line the first def starts at; seen: the line before was one
def first_def(ls: List<&2, String>, seen: Bool, +i: Nat) -> Nat:
  match ls seen:
    case Nil{} True{}:
      Nat.sub(i, 1n)
    case Nil{} False{}:
      i
    case Con{l, r} True{}:
      Nat.sub(i, 1n)
    case Con{+l, r} False{}:
      first_def(r, String.starts_with(l, "def "), 1n+i)

# how many lines lead with '#'; on: still counting
def lead_comments(ls: List<&2, String>, on: Bool, +n: Nat) -> Nat:
  match ls on:
    case Nil{} _:
      n
    case Con{l, r} False{}:
      n
    case Con{+l, r} True{}:
      lead_comments(r, String.starts_with(l, "#"), Nat.add(n, Bool.pick(Nat, String.starts_with(l, "#"), 1n, 0n)))

# where the first def starts, with the comment over it
def helpers_at(+ls: List<&2, String>) -> Nat:
  Nat.sub(first_def(ls, False{}, 0n), lead_comments(List.reverse(&2, String, K.ltake(ls, first_def(ls, False{}, 0n))), True{}, 0n))

# ---- the whole rewrite ----

def insert_helpers(+text: String, +h: String) -> String:
  +ls = String.lines(text)
  String.concat([String.join(K.ltake(ls, helpers_at(ls)), "\n"), "\n", h, "\n", String.join(K.ldrop(ls, helpers_at(ls)), "\n")])

def pair.msg(+d: String, +p: Pd, +bn: String, +okn: String, +abs: List<&2, Ab>) -> String:
  String.concat(["paired ", d, ": (", okn, ", ", bn, ") -> ", d, ".pair(", bn, ", ", String.join(Pd.eargs(p), ", "),
    "); lemmas about it: ", String.join(ab_names(abs), ", ")])

type Lf is Data:
  Lf{env: List<&2, K.Kv>, leaf: String}

def Lf.env(x: Lf) -> List<&2, K.Kv>:
  match x:
    case Lf{e, l}:
      e

def Lf.leaf(x: Lf) -> String:
  match x:
    case Lf{e, l}:
      l

def simple_name(+x: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(x)), String.eq(C.first_of(C.tokens(x)), x))

def let_lhs(+t: String) -> String:
  C.strip_q(String.trim(String.take(t, C.or_len(C.find(t, " = "), 0n))))

def is_let(+l: String) -> Bool:
  Bool.and(String.contains(String.trim(l), " = "), simple_name(let_lhs(String.trim(l))))

def lf.line(islet: Bool, blank: Bool, +l: String, +acc: Lf) -> Lf:
  match islet blank:
    case True{} _:
      Lf{K.Kv{let_lhs(String.trim(l)), K.subst_vars(String.drop(String.trim(l), Nat.add(3n, C.or_len(C.find(String.trim(l), " = "), 0n))), Lf.env(acc))} <> Lf.env(acc), Lf.leaf(acc)}
    case False{} True{}:
      acc
    case False{} False{}:
      Lf{Lf.env(acc), String.concat([Lf.leaf(acc), " ", String.trim(l)])}

def lf.go(ls: List<&2, String>, acc: Lf) -> Lf:
  match ls:
    case Nil{}:
      acc
    case +l <> r:
      lf.go(r, lf.line(is_let(l), String.is_empty(String.trim(l)), l, acc))

# the expression a case body ends in, with its lets put in
def leaf_of(+body: String) -> String:
  String.trim(K.subst_vars(Lf.leaf(lf.go(String.lines(body), Lf{Nil{}, SNil{}})), Lf.env(lf.go(String.lines(body), Lf{Nil{}, SNil{}}))))

def keep.pick(skip: Bool, +x: String, rest: List<&2, String>) -> List<&2, String>:
  match skip:
    case True{}:
      rest
    case False{}:
      x <> rest

# the params other than n (index 0), ok (k) and b (k+1)
def others(ns: List<&2, String>, +i: Nat, +k: Nat) -> List<&2, String>:
  match ns:
    case Nil{}:
      Nil{}
    case +n <> r:
      keep.pick(Bool.or(Nat.is_eq(i, 0n), Bool.or(Nat.is_eq(i, k), Nat.is_eq(i, 1n+k))), String.trim(n), others(r, 1n+i, k))

def others_of(+ns: List<&2, String>, +k: Nat) -> List<&2, String>:
  others(ns, 0n, k)

def same.fin(+leaf: String, +bn: String, +d: String, +k: Nat) -> String:
  Bool.pick(String, String.eq(leaf, bn), "      {==}",
    String.concat(["      ", d, ".same(", C.nth(K.trims(K.first_args(leaf, d)), 0n), ", ", C.nth(K.trims(K.first_args(leaf, d)), k), ", ",
      C.nth(K.trims(K.first_args(leaf, d)), 1n+k), ", ", String.join(others_of(K.trims(K.first_args(leaf, d)), k), ", "), ", {==})"]))

def rb_n(+rb: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(rb), 0n)

def same.case(+cs: List<&2, K.Case>, +ncls: String, +okv: String, +d: String, +p: Pd, +bn: String, +rest: String, +rb: String,
  +rt: String) -> String:
  String.concat(["    case ", ncls, " ", okv, "{} ", K.open_pat(Pd.rec(p), rb_n(rb)), ":\n",
    "      %Equal.sym(Bool, ", K.call_text(Pd.g(p), K.rebuilt(Pd.rec(p), rb_n(rb)) <> Pd.eargs(p)), ", ", okv, "{}, e)\n",
    "        : {", d, "(", ncls, ", (", K.rebuilt(Pd.rec(p), rb_n(rb)), ", _), ", rest, ") == ", d, ".old(", ncls, ", ", okv, "{}, ",
    K.rebuilt(Pd.rec(p), rb_n(rb)), ", ", rest, ") : ", rt, "}\n",
    same.fin(leaf_of(pick_case(cs, ncls, okv)), bn, d, Pd.k(p))])

def same.cases(+cs: List<&2, K.Case>, +d: String, +p: Pd, +bn: String, +rest: String, +nf: String, +rt: String) -> String:
  String.join([same.case(cs, "0n", "True", d, p, bn, rest, nf, rt), same.case(cs, "0n", "False", d, p, bn, rest, nf, rt),
    same.case(cs, succ_pat(cs), "True", d, p, bn, rest, nf, rt), same.case(cs, succ_pat(cs), "False", d, p, bn, rest, nf, rt)], "\n")

def old_def(+b: String, +d: String) -> String:
  K.rewrite_calls(String.append(String.concat(["def ", d, ".old("]), String.drop(b, Nat.add(5n, String.length(d)))), d,
    K.Ren{String.append(d, ".old")})

# D.same: for every n, ok and b with G(b, e..) == ok, the new D on the
# pair of b is the old D on (ok, b)
def pair.same(+phys2: String, +b: String, +d: String, +p: Pd, +recs: List<&2, K.Rec>) -> String:
  +ps = C.Sig.ps(C.sig_of(b))
  +names = C.names(ps)
  +bn = C.nth(names, 1n+Pd.k(p))
  +okn = C.nth(names, Pd.k(p))
  +rest = String.join(others_of(names, Pd.k(p)), ", ")
  +cs = cases_of_match(b, String.trim(K.first_code(String.lines(K.body_of(b)))))
  String.concat([phys2, "\n\n", old_def(b, d), "\n",
    "def ", d, ".same(", String.join(List.append(&2, String, [String.trim(C.nth(ps, 0n)), String.trim(C.nth(ps, Pd.k(p))),
      String.concat([bn, ": ", Pd.rec(p)])], others(ps, 0n, Pd.k(p))), ", "),
    ", e: {", K.call_text(Pd.g(p), bn <> Pd.eargs(p)), " == ", okn, " : Bool})\n",
    "  -> {", d, "(", C.nth(names, 0n), ", ", K.call_text(String.append(d, ".pair"), bn <> Pd.eargs(p)), ", ", rest, ") == ",
    d, ".old(", C.nth(names, 0n), ", ", okn, ", ", bn, ", ", rest, ") : ", F.ret_type(b), "}:\n",
    "  match ", C.nth(names, 0n), " ", okn, " ", bn, ":\n",
    same.cases(cs, d, p, bn, rest, Nat.show(List.length(&2, String, K.fields_of(recs, Pd.rec(p)))), F.ret_type(b)), "\n"])

def pair.make(+p: Pd, +phys: String, +proof: String, +d: String, +b: String, +recs: List<&2, K.Rec>) -> K.Plan:
  +ps = C.Sig.ps(C.sig_of(b))
  +names = C.names(ps)
  +al = C.alias_of(proof)
  +qr = String.concat([al, ".", Pd.rec(p)])
  +qd = String.concat([al, ".", d])
  +pbs = C.blocks(proof)
  +abs = abouts(pbs, qd, Pd.k(p), qr)
  +cx = {Cx{Pd.k(p), qd, String.concat([al, ".", Pd.g(p)]), String.concat([al, ".", d, ".pair"]), qr,
    String.append(Pd.rec(p), ".of_pair"), String.append(d, ".pair_up"), abs} : Cx}
  +phys2 = String.join(phys_blocks(C.blocks(phys), d, new_def(b, d, p, recs), K.PairArgs{Pd.k(p), Pd.g(p), String.append(d, ".pair")}), "\n")
  K.Plan{True{}, pair.msg(d, p, C.nth(names, 1n+Pd.k(p)), C.nth(names, Pd.k(p)), abs), phys2,
    insert_helpers(String.join(proof_blocks(pbs, cx), "\n"),
      helpers(cx, d, Pd.eargs(p), chunks_of(Pd.eargs(p), ps), List.length(&2, String, K.fields_of(recs, Pd.rec(p))), al,
        type_names(C.blocks(phys)))),
    pair.same(phys2, b, d, p, recs)}

def pair.shape(ok: Bool, +p: Pd, +phys: String, +proof: String, +d: String, +b: String, +recs: List<&2, K.Rec>) -> K.Plan:
  match ok:
    case True{}:
      pair.make(p, phys, proof, d, b, recs)
    case False{}:
      K.refuse(String.concat([d, ": its body is not one match over its Nat and its Bool"]))

def pair.found(ok: Bool, +p: Pd, +phys: String, +proof: String, +d: String, +b: String, +recs: List<&2, K.Rec>) -> K.Plan:
  match ok:
    case True{}:
      pair.shape(String.eq(String.trim(K.first_code(String.lines(K.body_of(b)))),
          String.concat(["match ", C.nth(C.names(C.Sig.ps(C.sig_of(b))), 0n), " ", C.nth(C.names(C.Sig.ps(C.sig_of(b))), Pd.k(p)), ":"])),
        p, phys, proof, d, b, recs)
    case False{}:
      K.refuse(String.concat([d, ": ", Pd.why(p)]))

def pair.exists(empty: Bool, +phys: String, +proof: String, +d: String, +b: String, +recs: List<&2, K.Rec>) -> K.Plan:
  match empty:
    case True{}:
      K.refuse(String.concat(["no def ", d, " in phys.bend"]))
    case False{}:
      pair.found(Pd.ok(pd.read(b, d, recs)), pd.read(b, d, recs), phys, proof, d, b, recs)

# both files rewritten, or why not; Plan.same is the equivalence for the checker
def pair.plan(+phys: String, +proof: String, +d: String) -> K.Plan:
  +recs = K.records(phys)
  +b = C.find_block(C.blocks(phys), String.concat(["def ", d, "("]))
  pair.exists(String.is_empty(b), phys, proof, d, b, recs)

# ---- the new def against the old one ----

# ---- in place ----

def pair.apply(ok: Bool, +dir: String, +pl: K.Plan) -> IO(String):
  match ok:
    case True{}:
      do IO<String>:
        u1 : Unit <- C.write_all(String.append(dir, "/phys.bend"), K.Plan.phys(pl))
        u2 : Unit <- C.write_all(String.append(dir, "/PROOF.bend"), K.Plan.proof(pl))
        return K.Plan.msg(pl)
    case False{}:
      IO.pure(String, String.append("not paired (the checker does not take D.same, see PAIRSAME_0.bend): ", K.Plan.msg(pl)))

def pair.checked(ok: Bool, +dir: String, +pl: K.Plan, +cap: Nat) -> IO(String):
  match ok:
    case True{}:
      do IO<String>:
        same : Bool <- L.check_one(dir, "PAIRSAME", K.Plan.same(pl), cap)
        pair.apply(same, dir, pl)
    case False{}:
      IO.pure(String, String.append("not paired: ", K.Plan.msg(pl)))

def pair.go(+dir: String, +pl: K.Plan, +cap: Nat) -> IO(String):
  pair.checked(K.Plan.ok(pl), dir, pl, cap)

# pairs <d>'s decision with its record, in <dir>, once D.same checks
def pair(+dir: String, +d: String, +cap: Nat) -> IO(String):
  do IO<String>:
    +phys : String <- C.read_all(String.append(dir, "/phys.bend"))
    +proof : String <- C.read_all(String.append(dir, "/PROOF.bend"))
    pair.go(dir, pair.plan(phys, proof, d), cap)

def fits.if(empty: Bool, +b: String, +d: String, +recs: List<&2, K.Rec>) -> Bool:
  match empty:
    case True{}:
      False{}
    case False{}:
      Bool.and(Pd.ok(pd.read(b, d, recs)),
        String.eq(String.trim(K.first_code(String.lines(K.body_of(b)))),
          String.concat(["match ", C.nth(C.names(C.Sig.ps(C.sig_of(b))), 0n), " ",
            C.nth(C.names(C.Sig.ps(C.sig_of(b))), Pd.k(pd.read(b, d, recs))), ":"])))

# whether the pair rewrite takes phys def d (its block b)
def pair.fits(+b: String, +d: String, +recs: List<&2, K.Rec>) -> Bool:
  fits.if(String.is_empty(b), b, d, recs)
