# Cubo -- proof optimizer, the once rewrite.
#
# A lemma concluding k(D(..)), with D a phys def that answers a record and
# k a claim that projects several of its fields: the checker, which shares
# nothing, normalizes the stuck D(..) once per field. The lemma, and every
# lemma its proof ends in that concludes the same way (its chain), states
# Once.R(k, D(..)) instead, which opens the record once and hands k the
# rebuilt record. Hypotheses about a record parameter become Once claims
# too, each call carries its argument over with Once.R.up, and a member
# called from outside keeps its old statement as a wrapper through
# Once.R.down. A phys def whose record parameter a transported claim reads
# field by field opens it once; S.same, for the checker, proves it equal
# to the old one.

import Base
import ./core.bend as C
import ./prof.bend as F
import ./calls.bend as K
import ./lift.bend as L
import ./pair.bend as P

# ---- text ----

def cc.go(s: String, here: Bool, +pat: String) -> Nat:
  match s here:
    case SNil{} _:
      0n
    case SCon{h, +t} True{}:
      1n+cc.go(t, K.call_at(t, pat, h), pat)
    case SCon{h, +t} False{}:
      cc.go(t, K.call_at(t, pat, h), pat)

# how many times pat starts in text after something that is not a name
def count_calls(+text: String, +pat: String) -> Nat:
  cc.go(text, K.call_at(text, pat, ' '), pat)

def hc.if(hit: Bool, +text: String, +pat: String) -> Bool:
  match hit:
    case True{}:
      Nat.is_le(1n, count_calls(text, pat))
    case False{}:
      False{}

def has_call(+text: String, +name: String) -> Bool:
  hc.if(String.contains(text, String.append(name, "(")), text, String.append(name, "("))

def rp.go(fuel: Nat, here: Bool, +s: String, +pat: String, +new: String) -> String:
  match fuel here:
    case 0n _:
      s
    case 1n+f True{}:
      String.append(new, rp.go(f, K.call_at(String.drop(s, String.length(pat)), pat, ')'), String.drop(s, String.length(pat)), pat, new))
    case 1n+f False{}:
      match s:
        case SNil{}:
          SNil{}
        case SCon{+h, +t}:
          SCon{h, rp.go(f, K.call_at(t, pat, h), t, pat, new)}

# every pat (a whole call, ending in ')') in s, not inside a longer name, becomes new
def repl_calls(+s: String, +pat: String, +new: String) -> String:
  rp.go(1n+String.length(s), K.call_at(s, pat, ' '), s, pat, new)

def drop_empty(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> +r:
      Bool.pick(List<&2, String>, String.is_empty(l), drop_empty(r), l <> r)

# the text without its first and last empty lines
def strip_nl(+s: String) -> String:
  String.join(List.reverse(&2, String, drop_empty(List.reverse(&2, String, drop_empty(String.lines(s))))), "\n")

# ---- record calls ----

type Rf is Data:
  Rf{ok: Bool, i: Nat, e: String, name: String, rec: String}

def Rf.ok(r: Rf) -> Bool:
  match r:
    case Rf{o, i, e, n, c}:
      o

def Rf.i(r: Rf) -> Nat:
  match r:
    case Rf{o, i, e, n, c}:
      i

def Rf.e(r: Rf) -> String:
  match r:
    case Rf{o, i, e, n, c}:
      e

def Rf.name(r: Rf) -> String:
  match r:
    case Rf{o, i, e, n, c}:
      n

def Rf.rec(r: Rf) -> String:
  match r:
    case Rf{o, i, e, n, c}:
      c

def rf.no() -> Rf:
  Rf{False{}, 0n, SNil{}, SNil{}, SNil{}}

def fns.pick(hit: Bool, +b: String, rest: List<&2, K.Kv>) -> List<&2, K.Kv>:
  match hit:
    case True{}:
      K.Kv{F.block_name(b), F.ret_type(b)} <> rest
    case False{}:
      rest

def fns.go(bs: List<&2, String>, +recs: List<&2, K.Rec>) -> List<&2, K.Kv>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> r:
      fns.pick(Bool.and(F.is_def(b), K.is_rec(recs, F.ret_type(b))), b, fns.go(r, recs))

# the phys defs that answer a record, and which record
def rec_fns(+phys: String, +recs: List<&2, K.Rec>) -> List<&2, K.Kv>:
  fns.go(C.blocks(phys), recs)

def rf.word(+s: String, +pat: String) -> String:
  K.take_word(String.drop(s, String.length(pat)))

def rf.here(+s: String, +pat: String, +prev: Char, +fns: List<&2, K.Kv>) -> Bool:
  Bool.and(K.call_at(s, pat, prev),
    Bool.and(K.next_is(String.drop(s, Nat.add(String.length(pat), String.length(rf.word(s, pat)))), '('),
      Maybe.is_some(&2, String, K.lookup(fns, rf.word(s, pat)))))

def rf.found(+s: String, +pat: String, +fns: List<&2, K.Kv>, +i: Nat) -> Rf:
  +w = rf.word(s, pat)
  +open = Nat.add(String.length(pat), String.length(w))
  Rf{True{}, i, String.take(s, Nat.add(open, Nat.add(2n, C.close_idx(String.drop(s, 1n+open), 0n)))), w,
    Maybe.default(&2, String, K.lookup(fns, w), SNil{})}

def rf.go(fuel: Nat, here: Bool, +s: String, +pat: String, +fns: List<&2, K.Kv>, +i: Nat) -> Rf:
  match fuel here:
    case 0n _:
      rf.no()
    case 1n+f True{}:
      rf.found(s, pat, fns, i)
    case 1n+f False{}:
      match s:
        case SNil{}:
          rf.no()
        case SCon{h, +t}:
          rf.go(f, rf.here(t, pat, h, fns), t, pat, fns, 1n+i)

# the first call al.D(..) in text of a phys def D that answers a record
def record_call(+text: String, +al: String, +fns: List<&2, K.Kv>) -> Rf:
  rf.go(1n+String.length(text), rf.here(text, String.append(al, "."), ' ', fns), text, String.append(al, "."), fns, 0n)

# ---- the tail expressions of a body ----

def is_match_body(+b: String) -> Bool:
  String.starts_with(String.trim(K.first_code(String.lines(b))), "match ")

def case_bodies(cs: List<&2, K.Case>) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> r:
      K.Case.body(c) <> case_bodies(r)

def body_cases(+b: String) -> List<&2, String>:
  +ls = String.lines(b)
  +first = K.first_code(ls)
  case_bodies(K.cases_at(K.after_line(ls, String.trim(first)), Nat.add(2n, String.length(K.ws_of(first)))))

# past a pattern's {..}, which nests nothing (close_idx only closes parens)
def after_brace(+r: String) -> String:
  Bool.pick(String, String.starts_with(r, "{"), String.drop(r, 1n+C.or_len(C.find(r, "}"), String.length(r))), r)

# x = .., +x = .., R{+a, +b} = ..
def is_let_line(+l: String) -> Bool:
  +t = C.strip_q(String.trim(l))
  Bool.and(Bool.not(String.starts_with(String.trim(l), "%")),
    Bool.and(Bool.not(String.is_empty(K.take_word(t))),
      String.starts_with(String.trim(after_brace(String.drop(t, String.length(K.take_word(t))))), "= ")))

# the lines a leaf is not: lets, rewrites and their `: T` lines
def skippable(+l: String) -> Bool:
  Bool.or(is_let_line(l), Bool.or(String.starts_with(String.trim(l), "%"), String.starts_with(String.trim(l), ":")))

def lf.drop.pick(hit: Bool, +l: String, +r: List<&2, String>, dropped: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      dropped
    case False{}:
      l <> r

def lf.drop(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> +r:
      lf.drop.pick(skippable(l), l, r, lf.drop(r))

def nonblank(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> r:
      P.keep.pick(String.is_empty(String.trim(l)), l, nonblank(r))

def leaf_line(+b: String) -> String:
  String.join(K.trims(lf.drop(nonblank(String.lines(b)))), " ")

def head_is_match(ws: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case +b <> r:
      is_match_body(b)

def lv(fuel: Nat, ws: List<&2, String>, ism: Bool) -> List<&2, String>:
  match fuel ws ism:
    case 0n _ _:
      Nil{}
    case 1n+f Nil{} _:
      Nil{}
    case 1n+f Con{+b, +r} True{}:
      lv(f, List.append(&2, String, body_cases(b), r), head_is_match(List.append(&2, String, body_cases(b), r)))
    case 1n+f Con{+b, +r} False{}:
      leaf_line(b) <> lv(f, r, head_is_match(r))

# through its matches, past its lets, what a body ends in
def leaves(+body: String) -> List<&2, String>:
  lv(1n+String.length(body), [body], is_match_body(body))

# ---- the chain ----

def lemma_of(+bs: List<&2, String>, +name: String) -> String:
  C.find_block(bs, String.concat(["def ", name, "("]))

# a lemma concluding a claim about the record r some phys def answers
def is_link(+bs: List<&2, String>, +name: String, +al: String, +fns: List<&2, K.Kv>, +r: String) -> Bool:
  +b = lemma_of(bs, name)
  Bool.and(Bool.not(String.is_empty(b)), Bool.and(Bool.not(String.is_empty(r)),
    Bool.and(String.eq(Rf.rec(record_call(K.conclusion(b), al, fns)), r),
      Bool.and(Bool.not(String.starts_with(K.conclusion(b), "Once.")), String.is_empty(lemma_of(bs, String.append(name, ".k1")))))))

def one_if(hit: Bool, +x: String) -> List<&2, String>:
  match hit:
    case True{}:
      [x]
    case False{}:
      Nil{}

def hot_in(hs: List<&2, String>, +lf: String, +m: String, +bs: List<&2, String>, +al: String, +fns: List<&2, K.Kv>, +r: String)
  -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case +h <> t:
      List.append(&2, String, one_if(Bool.and(Bool.not(String.eq(h, m)), Bool.and(has_call(lf, h), is_link(bs, h, al, fns, r))), h),
        hot_in(t, lf, m, bs, al, fns, r))

# the lemma a leaf ends in, and every hot lemma it calls, when they conclude the same way
def next_leaf(+lf: String, +m: String, +bs: List<&2, String>, +al: String, +fns: List<&2, K.Kv>, +hot: List<&2, String>, +r: String)
  -> List<&2, String>:
  +w = K.take_word(lf)
  List.append(&2, String,
    one_if(Bool.and(K.next_is(String.drop(lf, String.length(w)), '('), Bool.and(Bool.not(String.eq(w, m)), is_link(bs, w, al, fns, r))), w),
    hot_in(hot, lf, m, bs, al, fns, r))

def next_all(ls: List<&2, String>, +m: String, +bs: List<&2, String>, +al: String, +fns: List<&2, K.Kv>, +hot: List<&2, String>, +r: String)
  -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +lf <> t:
      List.append(&2, String, next_leaf(lf, m, bs, al, fns, hot, r), next_all(t, m, bs, al, fns, hot, r))

def next_of(+m: String, +bs: List<&2, String>, +al: String, +fns: List<&2, K.Kv>, +hot: List<&2, String>, +r: String) -> List<&2, String>:
  next_all(leaves(K.body_of(lemma_of(bs, m))), m, bs, al, fns, hot, r)

def head_fresh(ws: List<&2, String>, +seen: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case +w <> t:
      Bool.not(C.mem(seen, w))

def chain.go(fuel: Nat, ws: List<&2, String>, fresh: Bool, +seen: List<&2, String>, +bs: List<&2, String>, +al: String,
  +fns: List<&2, K.Kv>, +hot: List<&2, String>, +r: String) -> List<&2, String>:
  match fuel ws fresh:
    case 0n _ _:
      seen
    case 1n+f Nil{} _:
      seen
    case 1n+f Con{w, +t} False{}:
      chain.go(f, t, head_fresh(t, seen), seen, bs, al, fns, hot, r)
    case 1n+f Con{+w, +t} True{}:
      chain.go(f, List.append(&2, String, t, next_of(w, bs, al, fns, hot, r)),
        head_fresh(List.append(&2, String, t, next_of(w, bs, al, fns, hot, r)), List.append(&2, String, seen, [w])),
        List.append(&2, String, seen, [w]), bs, al, fns, hot, r)

# ---- each member ----

type Mb is Data:
  Mb{name: String, e: String, lam: String, lnames: List<&2, String>, hyps: List<&2, K.Hy>, head: String, out: Bool, tv: String}

def Mb.name(m: Mb) -> String:
  match m:
    case Mb{n, e, l, ns, hs, h, o, v}:
      n

def Mb.e(m: Mb) -> String:
  match m:
    case Mb{n, e, l, ns, hs, h, o, v}:
      e

def Mb.lam(m: Mb) -> String:
  match m:
    case Mb{n, e, l, ns, hs, h, o, v}:
      l

def Mb.lnames(m: Mb) -> List<&2, String>:
  match m:
    case Mb{n, e, l, ns, hs, h, o, v}:
      ns

def Mb.hyps(m: Mb) -> List<&2, K.Hy>:
  match m:
    case Mb{n, e, l, ns, hs, h, o, v}:
      hs

def Mb.head(m: Mb) -> String:
  match m:
    case Mb{n, e, l, ns, hs, h, o, v}:
      h

def Mb.out(m: Mb) -> Bool:
  match m:
    case Mb{n, e, l, ns, hs, h, o, v}:
      o

def Mb.tv(m: Mb) -> String:
  match m:
    case Mb{n, e, l, ns, hs, h, o, v}:
      v

def k1_of(+m: Mb) -> String:
  Bool.pick(String, Mb.out(m), String.append(Mb.name(m), ".k1"), Mb.name(m))

# ofp(w) in t, or nothing
def ofp_tgt(+t: String, +ofp: String) -> String:
  +after = String.drop(t, Nat.add(C.or_len(C.find(t, String.append(ofp, "(")), 0n), 1n+String.length(ofp)))
  Bool.pick(String,
    Bool.and(String.contains(t, String.append(ofp, "(")),
      Bool.and(Bool.not(String.is_empty(K.take_word(after))), K.next_is(String.drop(after, String.length(K.take_word(after))), ')'))),
    String.concat([ofp, "(", K.take_word(after), ")"]), SNil{})

# the first record parameter named in t, other than the one t is the type of
def rec_tgt(rp: List<&2, String>, +t: String, +me: String) -> String:
  match rp:
    case Nil{}:
      SNil{}
    case +v <> r:
      Bool.pick(String, Bool.and(C.mem(C.tokens(t), v), Bool.not(String.eq(v, me))), v, rec_tgt(r, t, me))

def tgt_of(+p: String, +ofp: String, +rp: List<&2, String>) -> String:
  Bool.pick(String, String.is_empty(ofp_tgt(K.ptype(p), ofp)), rec_tgt(rp, K.ptype(p), C.pname(p)), ofp_tgt(K.ptype(p), ofp))

def hyp_lam(+t: String, +tgt: String, +qr: String) -> String:
  String.concat(["(kb: ", qr, ") => ",
    Bool.pick(String, String.ends_with(tgt, ")"), repl_calls(t, tgt, "kb"), K.subst_vars(t, [K.Kv{tgt, "kb"}]))])

def hy.pick(hit: Bool, h: K.Hy, rest: List<&2, K.Hy>) -> List<&2, K.Hy>:
  match hit:
    case True{}:
      h <> rest
    case False{}:
      rest

# the parameters that are claims about a record, and about which
def hyps.go(ps: List<&2, String>, +i: Nat, +ofp: String, +rp: List<&2, String>, +qr: String) -> List<&2, K.Hy>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> r:
      hy.pick(Bool.and(Bool.not(String.is_empty(tgt_of(p, ofp, rp))), Bool.not(String.eq(K.ptype(p), qr))),
        K.Hy{i, tgt_of(p, ofp, rp), hyp_lam(K.ptype(p), tgt_of(p, ofp, rp), qr)}, hyps.go(r, 1n+i, ofp, rp, qr))

def rec_params(ps: List<&2, String>, +qr: String) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> r:
      P.keep.pick(Bool.not(String.eq(K.ptype(p), qr)), C.pname(p), rec_params(r, qr))

# the first hypothesis about a bare parameter the concluding call reads
def tr.hy(hs: List<&2, K.Hy>, +lnames: List<&2, String>, +e: String) -> String:
  match hs:
    case Nil{}:
      SNil{}
    case +h <> r:
      Bool.pick(String, Bool.and(C.mem(lnames, K.Hy.tgt(h)), C.mem(C.tokens(e), K.Hy.tgt(h))), K.Hy.tgt(h), tr.hy(r, lnames, e))

def mb.make(+name: String, +c: String, +rf: Rf, +ps: List<&2, String>, +ofp: String, +qr: String, +out: Bool) -> Mb:
  +hs = hyps.go(ps, 0n, ofp, rec_params(ps, qr), qr)
  Mb{name, Rf.e(rf), String.concat(["(kb: ", qr, ") => ", String.take(c, Rf.i(rf)), "kb", String.drop(c, Nat.add(Rf.i(rf), String.length(Rf.e(rf))))]),
    C.names(ps), hs, Rf.name(rf), out, tr.hy(hs, C.names(ps), Rf.e(rf))}

def mb.of(+name: String, +b: String, +al: String, +fns: List<&2, K.Kv>, +qr: String, +ofp: String, +out: Bool) -> Mb:
  mb.make(name, K.conclusion(b), record_call(K.conclusion(b), al, fns), C.Sig.ps(C.sig_of(b)), ofp, qr, out)

def out.go(bs: List<&2, String>, +s: List<&2, String>, +m: String) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case +b <> r:
      Bool.or(Bool.and(Bool.not(C.mem(s, F.block_name(b))), has_call(b, m)), out.go(r, s, m))

def members(ns: List<&2, String>, +all: List<&2, String>, +bs: List<&2, String>, +al: String, +fns: List<&2, K.Kv>, +qr: String,
  +ofp: String) -> List<&2, Mb>:
  match ns:
    case Nil{}:
      Nil{}
    case +n <> r:
      mb.of(n, lemma_of(bs, n), al, fns, qr, ofp, out.go(bs, all, n)) <> members(r, all, bs, al, fns, qr, ofp)

def conv_names(ms: List<&2, Mb>) -> List<&2, String>:
  match ms:
    case Nil{}:
      Nil{}
    case +m <> r:
      k1_of(m) <> (Mb.name(m) <> conv_names(r))

def mine.go(hs: List<&2, K.Hy>, +ns: List<&2, String>) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case +h <> r:
      C.nth(ns, K.Hy.idx(h)) <> mine.go(r, ns)

def find_mb(ms: List<&2, Mb>, +n: String) -> Maybe<&2, Mb>:
  match ms:
    case Nil{}:
      None{}
    case +m <> r:
      Bool.pick(Maybe<&2, Mb>, String.eq(Mb.name(m), n), Some{m}, find_mb(r, n))

# ---- rewriting the members ----

type Ox is Data:
  Ox{qr: String, once: String, down: String, up: String, nf: Nat, conv: List<&2, String>}

def Ox.qr(x: Ox) -> String:
  match x:
    case Ox{q, o, d, u, n, c}:
      q

def Ox.once(x: Ox) -> String:
  match x:
    case Ox{q, o, d, u, n, c}:
      o

def Ox.down(x: Ox) -> String:
  match x:
    case Ox{q, o, d, u, n, c}:
      d

def Ox.up(x: Ox) -> String:
  match x:
    case Ox{q, o, d, u, n, c}:
      u

def Ox.nf(x: Ox) -> Nat:
  match x:
    case Ox{q, o, d, u, n, c}:
      n

def Ox.conv(x: Ox) -> List<&2, String>:
  match x:
    case Ox{q, o, d, u, n, c}:
      c

def ren_if(out: Bool, +t: String, +name: String) -> String:
  match out:
    case True{}:
      K.rewrite_calls(t, name, K.Ren{String.append(name, ".k1")})
    case False{}:
      t

# each call of a member carries its record hypotheses over with up
def conv.go(ms: List<&2, Mb>, +t: String, +mine: List<&2, String>, +cx: Ox) -> String:
  match ms:
    case Nil{}:
      t
    case +m <> r:
      conv.go(r, ren_if(Mb.out(m),
        K.rewrite_calls(t, Mb.name(m), K.OnceArgs{Mb.hyps(m), mine, Ox.conv(cx), Mb.lnames(m), Ox.up(cx)}), Mb.name(m)), mine, cx)

def once_p(m: Maybe<&2, K.Hy>, +p: String, +once: String) -> String:
  match m:
    case None{}:
      p
    case Some{+h}:
      String.concat([C.first_of(String.split(p, ':')), ": ", once, "(", K.Hy.lam(h), ", ", K.Hy.tgt(h), ")"])

def once_ps(ps: List<&2, String>, +i: Nat, +hs: List<&2, K.Hy>, +once: String) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> r:
      once_p(K.hy_at(hs, i), p, once) <> once_ps(r, 1n+i, hs, once)

def tr.line(+l: String, +v: String, +op: String) -> List<&2, String>:
  Bool.pick(List<&2, String>, K.is_case_at(l, "    "),
    [l, String.concat(["      match ", v, ":"]), String.concat(["        case ", op, ":"])],
    [Bool.pick(String, Bool.and(String.starts_with(l, "      "), Bool.not(String.is_empty(String.trim(l)))), String.append("    ", l), l)])

def tr.lines(ls: List<&2, String>, +v: String, +op: String) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> r:
      List.append(&2, String, tr.line(l, v, op), tr.lines(r, v, op))

# the record v opened in each top case, or around the whole body
def transport(+bd: String, +v: String, +op: String) -> String:
  Bool.pick(String,
    Bool.and(String.starts_with(String.trim(K.first_code(String.lines(bd))), "match "), String.starts_with(K.first_code(String.lines(bd)), "  match")),
    String.join(tr.lines(String.lines(bd), v, op), "\n"),
    String.concat(["\n  match ", v, ":\n    case ", op, ":\n", K.indent(strip_nl(bd), 4n), "\n"]))

# the body opens v already (the rule ran on it before)
def opened_in(+bd: String, +v: String, +op: String) -> Bool:
  Bool.and(String.contains(bd, String.concat(["match ", v, ":"])), String.contains(bd, String.concat(["case ", C.first_of(String.split(op, '{')), "{"])))

def transport.if(hit: Bool, +bd: String, +v: String, +op: String) -> String:
  match hit:
    case True{}:
      bd
    case False{}:
      transport(bd, v, op)

def rename_def(+s: String, +n: String, +n2: String) -> String:
  String.concat(["def ", n2, "(", String.drop(s, Nat.add(5n, String.length(n)))])

def wrap_ps(ps: List<&2, String>, +ew: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> r:
      Bool.pick(String, Bool.and(C.mem(ew, C.pname(p)), Bool.not(C.starts_q(String.trim(p)))), C.add_plus(p), p) <> wrap_ps(r, ew)

def wrap_arg(m: Maybe<&2, K.Hy>, +n: String, +up: String) -> String:
  match m:
    case None{}:
      n
    case Some{+h}:
      String.concat([up, "(", K.Hy.lam(h), ", ", K.Hy.tgt(h), ", ", n, ")"])

def wrap_args(ns: List<&2, String>, +i: Nat, +hs: List<&2, K.Hy>, +up: String) -> List<&2, String>:
  match ns:
    case Nil{}:
      Nil{}
    case +n <> r:
      wrap_arg(K.hy_at(hs, i), n, up) <> wrap_args(r, 1n+i, hs, up)

# the old statement, proven from the member through down
def wrapper(+b: String, +m: Mb, +cx: Ox) -> String:
  String.concat([K.with_params(C.sig_part(b), wrap_ps(C.Sig.ps(C.sig_of(b)), C.tokens(Mb.e(m)))), "\n  ", Ox.down(cx), "(", Mb.lam(m), ", ",
    Mb.e(m), ",\n    ", k1_of(m), "(", String.join(wrap_args(Mb.lnames(m), 0n, Mb.hyps(m), Ox.up(cx)), ", "), "))\n"])

def wrapper.if(out: Bool, +b: String, +m: Mb, +cx: Ox) -> String:
  match out:
    case True{}:
      String.append("\n", wrapper(b, m, cx))
    case False{}:
      SNil{}

def mb.block(+b: String, +m: Mb, +ms: List<&2, Mb>, +cx: Ox) -> String:
  +s2 = K.set_conclusion(K.with_params(C.sig_part(b), once_ps(C.Sig.ps(C.sig_of(b)), 0n, Mb.hyps(m), Ox.once(cx))),
    String.concat([Ox.once(cx), "(", Mb.lam(m), ", ", Mb.e(m), ")"]))
  String.concat([rename_def(s2, Mb.name(m), k1_of(m)),
    transport.if(Bool.or(String.is_empty(Mb.tv(m)), opened_in(K.body_of(b), Mb.tv(m), K.open_pat(Ox.qr(cx), Ox.nf(cx)))),
      conv.go(ms, K.body_of(b), mine.go(Mb.hyps(m), Mb.lnames(m)), cx), Mb.tv(m), K.open_pat(Ox.qr(cx), Ox.nf(cx))),
    wrapper.if(Mb.out(m), b, m, cx)])

def ob.one(m: Maybe<&2, Mb>, +b: String, +ms: List<&2, Mb>, +cx: Ox) -> String:
  match m:
    case None{}:
      b
    case Some{x}:
      mb.block(b, x, ms, cx)

def out_blocks(bs: List<&2, String>, +ms: List<&2, Mb>, +cx: Ox) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> r:
      ob.one(find_mb(ms, F.block_name(b)), b, ms, cx) <> out_blocks(r, ms, cx)

def once_helpers(+cx: Ox) -> String:
  +q = Ox.qr(cx)
  +o = Ox.once(cx)
  +op = K.open_pat(q, Ox.nf(cx))
  String.concat([
    "def ", o, "(k: ", q, " -> Type, b: ", q, ") -> Type:\n  match b:\n    case ", op, ":\n      k(", K.rebuilt(q, Ox.nf(cx)), ")\n\n",
    "def ", Ox.down(cx), "(-k: ", q, " -> Type, b: ", q, ", h: ", o, "(k, b)) -> k(b):\n  match b:\n    case ", op, ":\n      h\n\n",
    "def ", Ox.up(cx), "(-k: ", q, " -> Type, b: ", q, ", h: k(b)) -> ", o, "(k, b):\n  match b:\n    case ", op, ":\n      h\n"])

def helpers.if(have: Bool, +text: String, +cx: Ox) -> String:
  match have:
    case True{}:
      text
    case False{}:
      P.insert_helpers(text, once_helpers(cx))

# ---- phys.bend: a def that reads a record parameter field by field opens it once ----

def reads(fs: List<&2, String>, +r: String, +v: String, +body: String) -> Nat:
  match fs:
    case Nil{}:
      0n
    case +f <> t:
      Nat.add(count_calls(body, String.concat([r, ".", f, "(", v, ")"])), reads(t, r, v, body))

def oo.pick(ps: List<&2, String>, +body: String, +recs: List<&2, K.Rec>) -> String:
  match ps:
    case Nil{}:
      SNil{}
    case +p <> r:
      Bool.pick(String,
        Bool.and(K.is_rec(recs, K.ptype(p)),
          Bool.and(Nat.is_le(2n, reads(K.fields_of(recs, K.ptype(p)), K.ptype(p), C.pname(p), body)),
            Bool.not(String.starts_with(String.trim(body), String.concat(["match ", C.pname(p), ":"]))))),
        p, oo.pick(r, body, recs))

# the record parameter of phys def d it would open, or nothing
def oo.param(+phys: String, +d: String, +recs: List<&2, K.Rec>) -> String:
  +b = C.find_block(C.blocks(phys), String.concat(["def ", d, "("]))
  oo.pick(C.Sig.ps(C.sig_of(b)), K.body_of(b), recs)

def sub_fields(fs: List<&2, String>, +i: Nat, +r: String, +v: String, +s: String) -> String:
  match fs:
    case Nil{}:
      s
    case +f <> t:
      sub_fields(t, 1n+i, r, v, repl_calls(s, String.concat([r, ".", f, "(", v, ")"]), String.append("u", Nat.show(1n+i))))

def unplus(ps: List<&2, String>, +v: String) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> r:
      Bool.pick(String, Bool.and(String.eq(C.pname(p), v), String.starts_with(String.trim(p), "+")),
        String.append(K.ws_of(p), String.drop(String.trim_start(p), 1n)), p) <> unplus(r, v)

def oo.block(+b: String, +p: String, +recs: List<&2, K.Rec>) -> String:
  +v = C.pname(p)
  +r = K.ptype(p)
  +nf = List.length(&2, String, K.fields_of(recs, r))
  String.concat([K.with_params(C.sig_part(b), unplus(C.Sig.ps(C.sig_of(b)), v)), "\n  match ", v, ":\n    case ", K.open_pat(r, nf), ":\n",
    K.indent(strip_nl(K.subst_vars(sub_fields(K.fields_of(recs, r), 0n, r, v, K.body_of(b)), [K.Kv{v, K.rebuilt(r, nf)}])), 4n), "\n"])

def open_one(+phys: String, +d: String, +recs: List<&2, K.Rec>) -> String:
  +bs = C.blocks(phys)
  +prefix = String.concat(["def ", d, "("])
  String.join(L.swap_block(bs, prefix, oo.block(C.find_block(bs, prefix), oo.param(phys, d, recs), recs)), "\n")

def open_all(os: List<&2, String>, +phys: String, +recs: List<&2, K.Rec>) -> String:
  match os:
    case Nil{}:
      phys
    case +o <> r:
      open_all(r, open_one(phys, o, recs), recs)

# d.same: the opened d is the old one, once the record is opened
def same_one(+phys: String, +d: String, +recs: List<&2, K.Rec>) -> String:
  +b = C.find_block(C.blocks(phys), String.concat(["def ", d, "("]))
  +v = C.pname(oo.param(phys, d, recs))
  +r = K.ptype(oo.param(phys, d, recs))
  +ns = String.join(C.names(C.Sig.ps(C.sig_of(b))), ", ")
  String.concat([P.old_def(b, d), "\n",
    "def ", d, ".same(", String.join(K.trims(unplus(C.Sig.ps(C.sig_of(b)), v)), ", "), ")\n",
    "  -> {", d, "(", ns, ") == ", d, ".old(", ns, ") : ", F.ret_type(b), "}:\n",
    "  match ", v, ":\n    case ", K.open_pat(r, List.length(&2, String, K.fields_of(recs, r))), ":\n      {==}\n"])

def same_all(os: List<&2, String>, +phys: String, +recs: List<&2, K.Rec>) -> List<&2, String>:
  match os:
    case Nil{}:
      Nil{}
    case +o <> r:
      same_one(phys, o, recs) <> same_all(r, phys, recs)

def opened.go(ms: List<&2, Mb>, +seen: List<&2, String>, +phys: String, +recs: List<&2, K.Rec>) -> List<&2, String>:
  match ms:
    case Nil{}:
      seen
    case +m <> r:
      opened.go(r,
        Bool.pick(List<&2, String>,
          Bool.or(String.is_empty(Mb.tv(m)), Bool.or(C.mem(seen, Mb.head(m)), String.is_empty(oo.param(phys, Mb.head(m), recs)))),
          seen, List.append(&2, String, seen, [Mb.head(m)])), phys, recs)

def same.if(none: Bool, +phys2: String, +phys: String, +os: List<&2, String>, +recs: List<&2, K.Rec>) -> String:
  match none:
    case True{}:
      SNil{}
    case False{}:
      String.concat([phys2, "\n\n", String.join(same_all(os, phys, recs), "\n")])

# ---- the lemmas the opening reaches ----

# the parameter of b that its statement hands q at index h, if a bare one
def reop.v(+b: String, +q: String, +h: Nat) -> String:
  +a = String.trim(C.nth(K.first_args(C.sig_part(b), q), h))
  Bool.pick(String, C.mem(C.names(C.Sig.ps(C.sig_of(b))), a), a, SNil{})

def reop.apply(+b: String, +v: String, +op: String, +rb: String) -> String:
  String.append(C.sig_part(b), transport(K.subst_vars(K.body_of(b), [K.Kv{v, rb}]), v, op))

def reop.if(keep: Bool, +b: String, +v: String, +op: String, +rb: String) -> String:
  match keep:
    case True{}:
      b
    case False{}:
      reop.apply(b, v, op, rb)

# not a def, no such parameter, opened already, or a wrapper of a .k1
def reop.keep(+b: String, +v: String, +bs: List<&2, String>, +skip: List<&2, String>, +op: String) -> Bool:
  Bool.or(Bool.not(F.is_def(b)), Bool.or(String.is_empty(v), Bool.or(C.mem(skip, F.block_name(b)),
    Bool.or(Bool.not(String.is_empty(lemma_of(bs, String.append(F.block_name(b), ".k1")))),
      Bool.or(C.mem(C.tokens(K.first_code(String.lines(K.body_of(b)))), v), opened_in(K.body_of(b), v, op))))))

def reop.blocks(ws: List<&2, String>, +bs: List<&2, String>, +skip: List<&2, String>, +q: String, +h: Nat, +op: String, +rb: String)
  -> List<&2, String>:
  match ws:
    case Nil{}:
      Nil{}
    case +b <> r:
      reop.if(reop.keep(b, reop.v(b, q, h), bs, skip, op), b, reop.v(b, q, h), op, rb) <> reop.blocks(r, bs, skip, q, h, op, rb)

# d opened its parameter at h: a lemma stating something about d on a record
# parameter of its own relied on d reading it field by field, so it opens it too
def reopen(+text: String, +phys: String, +d: String, +recs: List<&2, K.Rec>, +al: String, +skip: List<&2, String>) -> String:
  +b = C.find_block(C.blocks(phys), String.concat(["def ", d, "("]))
  +p = oo.param(phys, d, recs)
  +qr = String.concat([al, ".", K.ptype(p)])
  +nf = List.length(&2, String, K.fields_of(recs, K.ptype(p)))
  String.join(reop.blocks(C.blocks(text), C.blocks(text), skip, String.concat([al, ".", d]),
    C.index_of(C.names(C.Sig.ps(C.sig_of(b))), C.pname(p)), K.open_pat(qr, nf), K.rebuilt(qr, nf)), "\n")

def reopen_all(os: List<&2, String>, +text: String, +phys: String, +recs: List<&2, K.Rec>, +al: String, +skip: List<&2, String>) -> String:
  match os:
    case Nil{}:
      text
    case +o <> r:
      reopen_all(r, reopen(text, phys, o, recs, al, skip), phys, recs, al, skip)

def moved_names(ms: List<&2, Mb>) -> List<&2, String>:
  match ms:
    case Nil{}:
      Nil{}
    case +m <> r:
      P.keep.pick(String.is_empty(Mb.tv(m)), k1_of(m), moved_names(r))

# ---- the whole rewrite ----

def k1_names(ms: List<&2, Mb>) -> List<&2, String>:
  match ms:
    case Nil{}:
      Nil{}
    case +m <> r:
      k1_of(m) <> k1_names(r)

def once.make(+phys: String, +proof: String, +l: String, +hot: List<&2, String>, +recs: List<&2, K.Rec>, +fns: List<&2, K.Kv>,
  +al: String, +bs: List<&2, String>, +r: String) -> K.Plan:
  +qr = String.concat([al, ".", r])
  +s = chain.go(Nat.add(8n, Nat.add(List.length(&2, String, bs), List.length(&2, String, bs))), [l], True{}, Nil{}, bs, al, fns, hot, r)
  +ms = members(s, s, bs, al, fns, qr, String.append(r, ".of_pair"))
  +cx = {Ox{qr, String.append("Once.", r), String.concat(["Once.", r, ".down"]), String.concat(["Once.", r, ".up"]),
    List.length(&2, String, K.fields_of(recs, r)), conv_names(ms)} : Ox}
  +text = String.join(out_blocks(bs, ms, cx), "\n")
  +os = opened.go(ms, Nil{}, phys, recs)
  +phys2 = open_all(os, phys, recs)
  K.Plan{True{}, String.concat(["once ", l, ": ", String.join(k1_names(ms), ", "), "; opened ", String.join(os, ", ")]),
    phys2, reopen_all(os, helpers.if(String.contains(text, String.concat(["def Once.", r, "("])), text, cx), phys, recs, al, moved_names(ms)),
    same.if(List.is_empty(&2, String, os), phys2, phys, os, recs)}

def once.link(ok: Bool, +phys: String, +proof: String, +l: String, +hot: List<&2, String>, +recs: List<&2, K.Rec>, +fns: List<&2, K.Kv>,
  +al: String, +bs: List<&2, String>, +r: String) -> K.Plan:
  match ok:
    case True{}:
      once.make(phys, proof, l, hot, recs, fns, al, bs, r)
    case False{}:
      K.refuse(String.concat([l, ": its conclusion is no claim about a record a phys def answers (or it is one already)"]))

# every file rewritten, or why not; Plan.same is S.same for each opened phys def
def once.plan(+phys: String, +proof: String, +l: String, +hot: List<&2, String>) -> K.Plan:
  +recs = K.records(phys)
  +fns = rec_fns(phys, recs)
  +al = C.alias_of(proof)
  +bs = C.blocks(proof)
  +r = Rf.rec(record_call(K.conclusion(lemma_of(bs, l)), al, fns))
  once.link(Bool.and(Bool.not(String.is_empty(r)), is_link(bs, l, al, fns, r)), phys, proof, l, hot, recs, fns, al, bs, r)

# ---- in place ----

def once.apply(ok: Bool, +dir: String, +pl: K.Plan) -> IO(String):
  match ok:
    case True{}:
      do IO<String>:
        u1 : Unit <- C.write_all(String.append(dir, "/phys.bend"), K.Plan.phys(pl))
        u2 : Unit <- C.write_all(String.append(dir, "/PROOF.bend"), K.Plan.proof(pl))
        return K.Plan.msg(pl)
    case False{}:
      IO.pure(String, String.append("not applied (the checker does not take S.same, see ONCESAME_0.bend): ", K.Plan.msg(pl)))

def once.same(none: Bool, +dir: String, +pl: K.Plan, +cap: Nat) -> IO(String):
  match none:
    case True{}:
      once.apply(True{}, dir, pl)
    case False{}:
      do IO<String>:
        same : Bool <- L.check_one(dir, "ONCESAME", K.Plan.same(pl), cap)
        once.apply(same, dir, pl)

def once.checked(ok: Bool, +dir: String, +pl: K.Plan, +cap: Nat) -> IO(String):
  match ok:
    case True{}:
      once.same(String.is_empty(K.Plan.same(pl)), dir, pl, cap)
    case False{}:
      IO.pure(String, String.append("not applied: ", K.Plan.msg(pl)))

def once.go(+dir: String, +pl: K.Plan, +cap: Nat) -> IO(String):
  once.checked(K.Plan.ok(pl), dir, pl, cap)

# states lemma l's chain once, in <dir>; hot: lemmas worth pulling in
def once(+dir: String, +l: String, +hot: List<&2, String>, +cap: Nat) -> IO(String):
  do IO<String>:
    +phys : String <- C.read_all(String.append(dir, "/phys.bend"))
    +proof : String <- C.read_all(String.append(dir, "/PROOF.bend"))
    once.go(dir, once.plan(phys, proof, l, hot), cap)

# ---- where once starts ----

def link_rec(+bs: List<&2, String>, +name: String, +al: String, +fns: List<&2, K.Kv>) -> String:
  Bool.pick(String, is_link(bs, name, al, fns, Rf.rec(record_call(K.conclusion(lemma_of(bs, name)), al, fns))),
    Rf.rec(record_call(K.conclusion(lemma_of(bs, name)), al, fns)), SNil{})

def links(hs: List<&2, String>, +bs: List<&2, String>, +al: String, +fns: List<&2, K.Kv>) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case +h <> r:
      P.keep.pick(String.is_empty(link_rec(bs, h, al, fns)), h, links(r, bs, al, fns))

def rest_of(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      t

# every lemma some chain of these takes in, other than where it starts
def inner_of(ls: List<&2, String>, +bs: List<&2, String>, +al: String, +fns: List<&2, K.Kv>, +hot: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> r:
      List.append(&2, String,
        rest_of(chain.go(Nat.add(8n, Nat.add(List.length(&2, String, bs), List.length(&2, String, bs))), [l], True{}, Nil{}, bs, al, fns, hot,
          link_rec(bs, l, al, fns))),
        inner_of(r, bs, al, fns, hot))

def outer(ls: List<&2, String>, +inner: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> r:
      P.keep.pick(C.mem(inner, l), l, outer(r, inner))

# the hot lemmas whose chain no other hot lemma's chain takes in
def roots(+hot: List<&2, String>, +phys: String, +proof: String) -> List<&2, String>:
  +bs = C.blocks(proof)
  +al = C.alias_of(proof)
  +fns = rec_fns(phys, K.records(phys))
  +ls = links(hot, bs, al, fns)
  outer(ls, inner_of(ls, bs, al, fns, hot))
