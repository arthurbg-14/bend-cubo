# Cubo -- proof optimizer, the abst rewrite.
#
# In a proof L, a call to another lemma, G(args), whose arguments hold the
# same stuck value T twice or more (a call of a def of phys.bend, of Base or
# of PROOF.bend's own, whose type is known): the checker, which shares
# nothing, normalizes every copy. The call moves into a new lemma
# L.tN, right above L, where T is its first parameter c: every proof inside the
# call whose statement speaks of T (a lemma call that does not hold T in
# its own arguments) becomes a hypothesis hc_i about c, and L.tN states
# what G states of these arguments, with c for T. L then calls L.tN with
# T once. Nothing of L's statement changes; the checker checks L.tN.

import Base
import ./core.bend as C
import ./prof.bend as F
import ./calls.bend as K
import ./pair.bend as P
import ./once.bend as O

# ---- text ----

def ch_head(s: String) -> Char:
  match s:
    case SNil{}:
      ' '
    case SCon{h, t}:
      h

def sw2(+w: String, +rest: String, +env: List<&2, K.Kv>) -> String:
  Bool.pick(String, Bool.or(String.contains(w, "."), K.next_is(rest, '{')), w, Maybe.default(&2, String, K.lookup(env, w), w))

def sv2.go(fuel: Nat, isw: Bool, +s: String, +env: List<&2, K.Kv>) -> String:
  match fuel isw:
    case 0n _:
      s
    case 1n+f True{}:
      String.append(sw2(K.take_word(s), String.drop(s, String.length(K.take_word(s))), env),
        sv2.go(f, K.head_word(String.drop(s, String.length(K.take_word(s)))), String.drop(s, String.length(K.take_word(s))), env))
    case 1n+f False{}:
      match s:
        case SNil{}:
          SNil{}
        case SCon{+h, +t}:
          SCon{h, sv2.go(f, K.head_word(t), t, env)}

# every bare name in env replaced, a called one too (a parameter k used as k(x))
def subst_p(+s: String, +env: List<&2, K.Kv>) -> String:
  sv2.go(1n+String.length(s), K.head_word(s), s, env)

# a name, or a call that is the whole text: it needs no parens around it
def simple_arg(+a: String) -> Bool:
  Bool.or(String.eq(K.take_word(a), a),
    Bool.and(Bool.not(String.is_empty(K.take_word(a))),
      Bool.and(K.next_is(String.drop(a, String.length(K.take_word(a))), '('),
        Nat.is_eq(Nat.add(String.length(K.take_word(a)), Nat.add(2n, C.close_idx(String.drop(a, 1n+String.length(K.take_word(a))), 0n))),
          String.length(a)))))

def env_val(+a: String) -> String:
  Bool.pick(String, simple_arg(a), a, String.concat(["(", a, ")"]))

def env_of(ns: List<&2, String>, +args: List<&2, String>, +i: Nat) -> List<&2, K.Kv>:
  match ns:
    case Nil{}:
      Nil{}
    case +n <> r:
      K.Kv{n, env_val(String.trim(C.nth(args, i)))} <> env_of(r, args, 1n+i)

def count_eq(ts: List<&2, String>, +t: String) -> Nat:
  match ts:
    case Nil{}:
      0n
    case +h <> r:
      Nat.add(Bool.pick(Nat, String.eq(h, t), 1n, 0n), count_eq(r, t))

# ---- the calls in a text ----

type Sp is Data:
  Sp{i: Nat, n: Nat, g: String}

def Sp.i(s: Sp) -> Nat:
  match s:
    case Sp{i, n, g}:
      i

def Sp.n(s: Sp) -> Nat:
  match s:
    case Sp{i, n, g}:
      n

def Sp.g(s: Sp) -> String:
  match s:
    case Sp{i, n, g}:
      g

def sp.is(start: Bool, +s: String, +defs: List<&2, String>) -> Bool:
  match start:
    case True{}:
      Bool.and(K.next_is(String.drop(s, String.length(K.take_word(s))), '('), C.mem(defs, K.take_word(s)))
    case False{}:
      False{}

def sp.here(+s: String, +prev: Char, +defs: List<&2, String>) -> Bool:
  sp.is(Bool.and(Bool.not(C.is_ident(prev)), K.head_word(s)), s, defs)

def sp.mk(+s: String, +i: Nat) -> Sp:
  +w = K.take_word(s)
  Sp{i, Nat.add(String.length(w), Nat.add(2n, C.close_idx(String.drop(s, 1n+String.length(w)), 0n))), w}

def sp.go(fuel: Nat, here: Bool, +s: String, +defs: List<&2, String>, +i: Nat) -> List<&2, Sp>:
  match fuel here:
    case 0n _:
      Nil{}
    case 1n+f True{}:
      sp.mk(s, i) <> sp.go(f, sp.here(String.drop(s, 1n), ch_head(s), defs), String.drop(s, 1n), defs, 1n+i)
    case 1n+f False{}:
      sp.go(f, sp.here(String.drop(s, 1n), ch_head(s), defs), String.drop(s, 1n), defs, 1n+i)

# every call in s of a name in defs, nested ones too, left to right
def spans(+s: String, +defs: List<&2, String>) -> List<&2, Sp>:
  sp.go(1n+String.length(s), sp.here(s, ' ', defs), s, defs, 0n)

def sp_text(+s: String, +sp: Sp) -> String:
  String.take(String.drop(s, Sp.i(sp)), Sp.n(sp))

# an expression on one line: its line breaks sit inside parens and mean nothing
def flat(+s: String) -> String:
  String.join(K.trims(String.lines(s)), " ")

# the call at sp, on one line
def ctext(+s: String, +sp: Sp) -> String:
  flat(sp_text(s, sp))

def pc.go(fuel: Nat, here: Bool, +s: String, +pat: String, +fns: List<&2, K.Kv>) -> List<&2, String>:
  match fuel here:
    case 0n _:
      Nil{}
    case 1n+f True{}:
      O.Rf.e(O.rf.found(s, pat, fns, 0n)) <> pc.go(f, O.rf.here(String.drop(s, 1n), pat, ch_head(s), fns), String.drop(s, 1n), pat, fns)
    case 1n+f False{}:
      pc.go(f, O.rf.here(String.drop(s, 1n), pat, ch_head(s), fns), String.drop(s, 1n), pat, fns)

def kc.is(start: Bool, +s: String, +known: List<&2, K.Kv>) -> Bool:
  match start:
    case True{}:
      Bool.and(K.next_is(String.drop(s, String.length(K.take_word(s))), '('), Maybe.is_some(&2, String, K.lookup(known, K.take_word(s))))
    case False{}:
      False{}

def kc.here(+s: String, +prev: Char, +known: List<&2, K.Kv>) -> Bool:
  kc.is(Bool.and(Bool.not(C.is_ident(prev)), K.head_word(s)), s, known)

def kc.go(fuel: Nat, here: Bool, +s: String, +known: List<&2, K.Kv>) -> List<&2, String>:
  match fuel here:
    case 0n _:
      Nil{}
    case 1n+f True{}:
      String.take(s, Sp.n(sp.mk(s, 0n))) <> kc.go(f, kc.here(String.drop(s, 1n), ch_head(s), known), String.drop(s, 1n), known)
    case 1n+f False{}:
      kc.go(f, kc.here(String.drop(s, 1n), ch_head(s), known), String.drop(s, 1n), known)

# every call in s of a def whose type is known, nested ones too
def known_calls(+s: String, +known: List<&2, K.Kv>) -> List<&2, String>:
  kc.go(1n+String.length(s), kc.here(s, ' ', known), s, known)

# a call with another call in its arguments: worth a parameter
def nests(+t: String) -> Bool:
  String.contains(String.drop(t, 1n+C.or_len(C.find(t, "("), 0n)), "(")

# the def behind a call, how long it is
def head_size(+t: String, +pbs: List<&2, String>) -> Nat:
  String.length(C.find_block(pbs, String.concat(["def ", String.drop(K.take_word(t), 1n+C.or_len(C.find(t, "."), 0n)), "("])))

# a record worth a parameter: another call inside it, or a def of some size behind it
def worth(+t: String, +pbs: List<&2, String>) -> Bool:
  Bool.or(nests(t), Nat.is_le(200n, head_size(t, pbs)))

def best.go(ts: List<&2, String>, +all: List<&2, String>, +cur: String, +pbs: List<&2, String>) -> String:
  match ts:
    case Nil{}:
      cur
    case +t <> r:
      best.go(r, all, Bool.pick(String, Bool.and(Nat.is_le(2n, count_eq(all, t)),
        Bool.and(Nat.is_lt(String.length(cur), String.length(t)), worth(t, pbs))), t, cur), pbs)

# the longest of these that nests and comes twice or more, or nothing
def best_t(+ts: List<&2, String>, +pbs: List<&2, String>) -> String:
  best.go(ts, ts, SNil{}, pbs)

# ---- context ----

type Ax is Data:
  Ax{al: String, fns: List<&2, K.Kv>, defs: List<&2, String>, bs: List<&2, String>, phys: String, types: List<&2, String>,
    pbs: List<&2, String>}

def Ax.al(x: Ax) -> String:
  match x:
    case Ax{a, f, d, b, p, t, q}:
      a

def Ax.fns(x: Ax) -> List<&2, K.Kv>:
  match x:
    case Ax{a, f, d, b, p, t, q}:
      f

def Ax.defs(x: Ax) -> List<&2, String>:
  match x:
    case Ax{a, f, d, b, p, t, q}:
      d

def Ax.bs(x: Ax) -> List<&2, String>:
  match x:
    case Ax{a, f, d, b, p, t, q}:
      b

def Ax.phys(x: Ax) -> String:
  match x:
    case Ax{a, f, d, b, p, t, q}:
      p

def Ax.types(x: Ax) -> List<&2, String>:
  match x:
    case Ax{a, f, d, b, p, t, q}:
      t

def Ax.pbs(x: Ax) -> List<&2, String>:
  match x:
    case Ax{a, f, d, b, p, t, q}:
      q

def def_names(bs: List<&2, String>) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> r:
      P.keep.pick(Bool.not(F.is_def(b)), F.block_name(b), def_names(r))

# what lemma g states of these arguments
def inst(+cx: Ax, +g: String, +args: List<&2, String>) -> String:
  +gb = O.lemma_of(Ax.bs(cx), g)
  flat(subst_p(K.conclusion(gb), env_of(C.names(C.Sig.ps(C.sig_of(gb))), args, 0n)))

def call_args(+ct: String, +g: String) -> List<&2, String>:
  K.trims(C.split_top(K.inner(ct, g), ','))

# ---- choosing the call ----

def qual.one(+sp: Sp, +body: String, +l: String, +cx: Ax) -> Bool:
  Bool.and(Bool.not(String.eq(Sp.g(sp), l)),
    Bool.and(Bool.not(O.has_call(sp_text(body, sp), l)),
      Bool.not(String.is_empty(best_t(known_calls(ctext(body, sp), Ax.fns(cx)), Ax.pbs(cx))))))

def sp.pick(hit: Bool, +sp: Sp, rest: List<&2, Sp>) -> List<&2, Sp>:
  match hit:
    case True{}:
      sp <> rest
    case False{}:
      rest

def qual(ss: List<&2, Sp>, +body: String, +l: String, +cx: Ax) -> List<&2, Sp>:
  match ss:
    case Nil{}:
      Nil{}
    case +sp <> r:
      sp.pick(qual.one(sp, body, l, cx), sp, qual(r, body, l, cx))

# b lies inside a, and is not a
def inside(+a: Sp, +b: Sp) -> Bool:
  Bool.and(Nat.is_le(Sp.i(a), Sp.i(b)),
    Bool.and(Nat.is_le(Nat.add(Sp.i(b), Sp.n(b)), Nat.add(Sp.i(a), Sp.n(a))), Bool.not(Bool.and(Nat.is_eq(Sp.i(a), Sp.i(b)), Nat.is_eq(Sp.n(a), Sp.n(b))))))

def has_inner(ss: List<&2, Sp>, +a: Sp) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case +b <> r:
      Bool.or(inside(a, b), has_inner(r, a))

def innermost(ss: List<&2, Sp>, +all: List<&2, Sp>) -> Maybe<&2, Sp>:
  match ss:
    case Nil{}:
      None{}
    case +a <> r:
      Bool.pick(Maybe<&2, Sp>, has_inner(all, a), innermost(r, all), Some{a})

def has_outer(ss: List<&2, Sp>, +a: Sp) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case +b <> r:
      Bool.or(inside(b, a), has_outer(r, a))

# ---- the proofs inside the call that speak of T ----

def outermost(ss: List<&2, Sp>, +all: List<&2, Sp>) -> List<&2, Sp>:
  match ss:
    case Nil{}:
      Nil{}
    case +a <> r:
      sp.pick(Bool.not(has_outer(all, a)), a, outermost(r, all))

def leaf.one(+sp: Sp, +ct: String, +t: String, +cx: Ax) -> Bool:
  Bool.and(Nat.is_lt(0n, Sp.i(sp)),
    Bool.and(Bool.not(String.contains(sp_text(ct, sp), t)),
      String.contains(inst(cx, Sp.g(sp), call_args(sp_text(ct, sp), Sp.g(sp))), t)))

def leaves(ss: List<&2, Sp>, +ct: String, +t: String, +cx: Ax) -> List<&2, Sp>:
  match ss:
    case Nil{}:
      Nil{}
    case +sp <> r:
      sp.pick(leaf.one(sp, ct, t, cx), sp, leaves(r, ct, t, cx))

def hc_name(+k: Nat) -> String:
  String.append("hc", Nat.show(k))

# the call with each leaf (left to right, numbered from k) turned into hc_k
def cut_leaves(hs: List<&2, Sp>, +ct: String, +k: Nat, +off: Nat) -> String:
  match hs:
    case Nil{}:
      String.drop(ct, off)
    case +h <> r:
      String.concat([String.take(String.drop(ct, off), Nat.sub(Sp.i(h), off)), hc_name(k), cut_leaves(r, ct, 1n+k, Nat.add(Sp.i(h), Sp.n(h)))])

def leaf_texts(hs: List<&2, Sp>, +ct: String) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case +h <> r:
      sp_text(ct, h) <> leaf_texts(r, ct)

def leaf_types(hs: List<&2, Sp>, +ct: String, +t: String, +c: String, +cx: Ax, +k: Nat) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case +h <> r:
      String.concat([hc_name(k), ": ", O.repl_calls(inst(cx, Sp.g(h), call_args(sp_text(ct, h), Sp.g(h))), t, c)])
        <> leaf_types(r, ct, t, c, cx, 1n+k)

# ---- the parameters the new lemma needs ----

type Pm is Data:
  Pm{name: String, chunk: String}

def Pm.name(p: Pm) -> String:
  match p:
    case Pm{n, c}:
      n

def Pm.chunk(p: Pm) -> String:
  match p:
    case Pm{n, c}:
      c

# the parameters, their types seen after the body's R{..} = v lines (v rebuilt from the fields)
def pms_of(ps: List<&2, String>, +env: List<&2, K.Kv>) -> List<&2, Pm>:
  match ps:
    case Nil{}:
      Nil{}
    case +p <> r:
      Pm{C.pname(p), String.concat([String.trim(C.first_of(String.split(p, ':'))), ": ", K.subst_vars(K.ptype(p), env)])} <> pms_of(r, env)

def rebuilt.one(+t: String, +cx: Ax) -> List<&2, K.Kv>:
  [K.Kv{String.trim(String.drop(t, Nat.add(4n, C.or_len(C.find(t, "} = "), 0n)))),
    String.concat([K.take_word(t), "{", String.join(C.names(C.split_top(String.take(String.drop(t, 1n+String.length(K.take_word(t))),
      Nat.sub(C.or_len(C.find(t, "}"), 0n), 1n+String.length(K.take_word(t)))), ',')), ", "), "}"])}]

def rebuilt.if(hit: Bool, +t: String, +cx: Ax) -> List<&2, K.Kv>:
  match hit:
    case True{}:
      rebuilt.one(t, cx)
    case False{}:
      Nil{}

def is_destructure(+t: String, +al: String) -> Bool:
  Bool.and(String.starts_with(t, String.append(al, ".")),
    Bool.and(K.next_is(String.drop(t, String.length(K.take_word(t))), '{'), String.contains(t, "} = ")))

# v and R{fields} for each R{..} = v line of a body
def rebuilt_env(ls: List<&2, String>, +cx: Ax) -> List<&2, K.Kv>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> r:
      List.append(&2, K.Kv, rebuilt.if(Bool.and(String.starts_with(l, "  "), Bool.and(Bool.not(String.starts_with(l, "   ")),
        is_destructure(String.trim(l), Ax.al(cx)))), String.trim(l), cx), rebuilt_env(r, cx))

def qual_types(fs: List<&2, String>, +al: String, +types: List<&2, String>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case +f <> r:
      P.qualify_one(K.ptype(f), al, types) <> qual_types(r, al, types)

def rec_types(+cx: Ax, +r: String) -> List<&2, String>:
  +line = C.first_of(K.ctor_lines(String.lines(C.find_block(C.blocks(Ax.phys(cx)), String.concat(["type ", r, " "])))))
  qual_types(C.split_top(String.take(String.drop(line, 1n+String.length(r)), Nat.sub(String.length(line), Nat.add(2n, String.length(r)))), ','),
    Ax.al(cx), Ax.types(cx))

def zip_pm(ns: List<&2, String>, +ts: List<&2, String>, +i: Nat) -> List<&2, Pm>:
  match ns:
    case Nil{}:
      Nil{}
    case +n <> r:
      Pm{n, String.concat([n, ": ", C.nth(ts, i)])} <> zip_pm(r, ts, 1n+i)

def let_pms.one(+t: String, +cx: Ax) -> List<&2, Pm>:
  +q = K.take_word(t)
  zip_pm(C.names(C.split_top(String.take(String.drop(t, 1n+String.length(q)), Nat.sub(C.or_len(C.find(t, "}"), 0n), 1n+String.length(q))), ',')),
    rec_types(cx, String.drop(q, 1n+String.length(Ax.al(cx)))), 0n)

def let_pms.if(hit: Bool, +t: String, +cx: Ax) -> List<&2, Pm>:
  match hit:
    case True{}:
      let_pms.one(t, cx)
    case False{}:
      Nil{}

# the fields a body's R{..} = v lines bind, typed from R
def let_pms(ls: List<&2, String>, +cx: Ax) -> List<&2, Pm>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> r:
      List.append(&2, Pm, let_pms.if(Bool.and(String.starts_with(l, "  "), Bool.and(Bool.not(String.starts_with(l, "   ")),
        is_destructure(String.trim(l), Ax.al(cx)))), String.trim(l), cx), let_pms(r, cx))

def pm.pick(hit: Bool, +p: Pm, rest: List<&2, Pm>) -> List<&2, Pm>:
  match hit:
    case True{}:
      p <> rest
    case False{}:
      rest

def needed(pms: List<&2, Pm>, +toks: List<&2, String>) -> List<&2, Pm>:
  match pms:
    case Nil{}:
      Nil{}
    case +p <> r:
      pm.pick(C.mem(toks, Pm.name(p)), p, needed(r, toks))

def chunk_toks(pms: List<&2, Pm>) -> List<&2, String>:
  match pms:
    case Nil{}:
      Nil{}
    case +p <> r:
      List.append(&2, String, C.tokens(Pm.chunk(p)), chunk_toks(r))

def pm_names(pms: List<&2, Pm>) -> List<&2, String>:
  match pms:
    case Nil{}:
      Nil{}
    case +p <> r:
      Pm.name(p) <> pm_names(r)

# the parameters the tokens name, and the ones their types name, and so on
def closure(n: Nat, +pms: List<&2, Pm>, +toks: List<&2, String>) -> List<&2, Pm>:
  match n:
    case 0n:
      needed(pms, toks)
    case 1n+m:
      closure(m, pms, List.append(&2, String, toks, chunk_toks(needed(pms, toks))))

def var_like(+t: String) -> Bool:
  Bool.and(Bool.not(String.contains(t, ".")), Bool.or(Char.is_lower(ch_head(t)), Char.is_eq(ch_head(t), '_')))

def bound_in(+t: String, +text: String) -> Bool:
  String.contains(text, String.concat(["(", t, ":"]))

# a name the new lemma could not know
def stray(ts: List<&2, String>, +known: List<&2, String>, +text: String) -> List<&2, String>:
  match ts:
    case Nil{}:
      Nil{}
    case +t <> r:
      P.keep.pick(Bool.not(Bool.and(var_like(t), Bool.not(Bool.or(C.mem(known, t), bound_in(t, text))))), t, stray(r, known, text))

def plus_if(+p: Pm, +body: String) -> String:
  Bool.pick(String, Bool.and(Nat.is_le(2n, count_eq(C.tokens(body), Pm.name(p))), Bool.not(C.starts_q(Pm.chunk(p)))),
    String.append("+", Pm.chunk(p)), Pm.chunk(p))

def chunks(pms: List<&2, Pm>, +body: String, +t: String, +c: String) -> List<&2, String>:
  match pms:
    case Nil{}:
      Nil{}
    case +p <> r:
      O.repl_calls(plus_if(p, body), t, c) <> chunks(r, body, t, c)

# ---- one rewrite ----

type Bd is Data:
  Bd{ok: Bool, why: String, helper: String, body: String}

def Bd.ok(b: Bd) -> Bool:
  match b:
    case Bd{o, w, h, n}:
      o

def Bd.why(b: Bd) -> String:
  match b:
    case Bd{o, w, h, n}:
      w

def Bd.helper(b: Bd) -> String:
  match b:
    case Bd{o, w, h, n}:
      h

def Bd.body(b: Bd) -> String:
  match b:
    case Bd{o, w, h, n}:
      n

def bd.no(+why: String) -> Bd:
  Bd{False{}, why, SNil{}, SNil{}}

def c_name(+ps: List<&2, Pm>) -> String:
  Bool.pick(String, C.mem(pm_names(ps), "c"), "c0", "c")

def build.fin(+stray: List<&2, String>, +name: String, +pms: List<&2, Pm>, +c: String, +cty: String, +hcs: List<&2, String>,
  +concl: String, +cbody: String, +body: String, +sp: Sp, +t: String, +htexts: List<&2, String>) -> Bd:
  Bool.pick(Bd, Bool.or(Bool.not(List.is_empty(&2, String, stray)), String.is_empty(String.trim(concl))),
    bd.no(String.concat(["no statement for the call, or names it cannot type: ", String.join(stray, ", ")])),
    Bd{True{}, SNil{},
      String.concat(["def ", name, "(", String.join(List.concat(&2, String, [
        [String.concat([Bool.pick(String, Nat.is_le(2n, count_eq(C.tokens(cbody), c)), "+", SNil{}), c, ": ", cty])], chunks(pms, cbody, t, c), hcs]), ", "),
        ")\n  -> ", concl, ":\n  ", cbody, "\n"]),
      String.concat([String.take(body, Sp.i(sp)), name, "(", String.join(List.concat(&2, String, [[t], pm_names(pms), htexts]), ", "), ")",
        String.drop(body, Nat.add(Sp.i(sp), Sp.n(sp)))])})

def hc_names(n: Nat, +k: Nat) -> List<&2, String>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      hc_name(k) <> hc_names(m, 1n+k)

# the call at sp moved into lemma `name`, with t as its parameter c
def build(+b: String, +sp: Sp, +t: String, +cx: Ax, +name: String) -> Bd:
  +body = K.body_of(b)
  +ct = ctext(body, sp)
  +hs = outermost(leaves(spans(ct, Ax.defs(cx)), ct, t, cx), leaves(spans(ct, Ax.defs(cx)), ct, t, cx))
  +all = List.append(&2, Pm, let_pms(String.lines(body), cx), pms_of(C.Sig.ps(C.sig_of(b)), rebuilt_env(String.lines(body), cx)))
  +c = c_name(all)
  +cbody = O.repl_calls(cut_leaves(hs, ct, 1n, 0n), t, c)
  +concl = O.repl_calls(inst(cx, Sp.g(sp), call_args(ct, Sp.g(sp))), t, c)
  +hcs = leaf_types(hs, ct, t, c, cx, 1n)
  +cty = Maybe.default(&2, String, K.lookup(Ax.fns(cx), K.take_word(t)), SNil{})
  +text = String.concat([cbody, " ", concl, " ", String.join(hcs, " ")])
  +pms = closure(4n, all, C.tokens(text))
  build.fin(stray(C.tokens(text), List.concat(&2, String, [pm_names(pms), [c], Ax.defs(cx), hc_names(List.length(&2, Sp, hs), 1n)]), text),
    name, pms, c, cty, hcs, concl, cbody, body, sp, t, leaf_texts(hs, ct))

def step.of(m: Maybe<&2, Sp>, +b: String, +cx: Ax, +name: String) -> Bd:
  match m:
    case None{}:
      bd.no("no call repeats a stuck record")
    case Some{+sp}:
      build(b, sp, best_t(known_calls(ctext(K.body_of(b), sp), Ax.fns(cx)), Ax.pbs(cx)), cx, name)

def t_len(+body: String, +sp: Sp, +cx: Ax) -> Nat:
  String.length(best_t(known_calls(ctext(body, sp), Ax.fns(cx)), Ax.pbs(cx)))

def max_t(ss: List<&2, Sp>, +body: String, +cx: Ax) -> Nat:
  match ss:
    case Nil{}:
      0n
    case +sp <> r:
      Nat.max(t_len(body, sp, cx), max_t(r, body, cx))

def of_len(ss: List<&2, Sp>, +body: String, +cx: Ax, +n: Nat) -> List<&2, Sp>:
  match ss:
    case Nil{}:
      Nil{}
    case +sp <> r:
      sp.pick(Nat.is_eq(t_len(body, sp, cx), n), sp, of_len(r, body, cx, n))

# the calls that repeat the biggest stuck record, and of those the innermost
def step(+b: String, +l: String, +cx: Ax, +name: String) -> Bd:
  +q = qual(spans(K.body_of(b), Ax.defs(cx)), K.body_of(b), l, cx)
  +big = of_len(q, K.body_of(b), cx, max_t(q, K.body_of(b), cx))
  step.of(innermost(big, big), b, cx, name)

# ---- a lemma, rewritten until no call is left to move ----

def free_name(fuel: Nat, +l: String, +k: Nat, +taken: List<&2, String>) -> String:
  match fuel:
    case 0n:
      String.concat([l, ".t", Nat.show(k)])
    case 1n+f:
      Bool.pick(String, C.mem(taken, String.concat([l, ".t", Nat.show(k)])), free_name(f, l, 1n+k, taken), String.concat([l, ".t", Nat.show(k)]))

def helper_name(+bd: Bd) -> String:
  F.block_name(Bd.helper(bd))

# the lemma just made, known from now on
def with_defs(+cx: Ax, +bd: Bd) -> Ax:
  Ax{Ax.al(cx), Ax.fns(cx), helper_name(bd) <> Ax.defs(cx), Bd.helper(bd) <> Ax.bs(cx), Ax.phys(cx), Ax.types(cx), Ax.pbs(cx)}

type Lr is Data:
  Lr{block: String, helpers: List<&2, String>}

def Lr.block(x: Lr) -> String:
  match x:
    case Lr{b, h}:
      b

def Lr.helpers(x: Lr) -> List<&2, String>:
  match x:
    case Lr{b, h}:
      h

def new_block(+b: String, +bd: Bd) -> String:
  String.append(C.sig_part(b), Bd.body(bd))

def lr.go(fuel: Nat, ok: Bool, +bd: Bd, +b: String, +l: String, +cx: Ax, +hs: List<&2, String>) -> Lr:
  match fuel ok:
    case 0n _:
      Lr{b, hs}
    case 1n+f False{}:
      Lr{b, hs}
    case 1n+f True{}:
      lr.go(f, Bd.ok(step(new_block(b, bd), l, with_defs(cx, bd), free_name(20n, l, 1n, List.append(&2, String, Ax.defs(cx), [helper_name(bd)])))),
        step(new_block(b, bd), l, with_defs(cx, bd), free_name(20n, l, 1n, List.append(&2, String, Ax.defs(cx), [helper_name(bd)]))),
        new_block(b, bd), l, with_defs(cx, bd), List.append(&2, String, hs, [Bd.helper(bd)]))

def lemma(+b: String, +l: String, +cx: Ax) -> Lr:
  lr.go(8n, Bd.ok(step(b, l, cx, free_name(20n, l, 1n, Ax.defs(cx)))), step(b, l, cx, free_name(20n, l, 1n, Ax.defs(cx))), b, l, cx, Nil{})

def out.one(hit: Bool, +b: String, +cx: Ax) -> String:
  match hit:
    case True{}:
      String.join(List.append(&2, String, Lr.helpers(lemma(b, F.block_name(b), cx)), [Lr.block(lemma(b, F.block_name(b), cx))]), "\n")
    case False{}:
      b

def out_blocks(bs: List<&2, String>, +ls: List<&2, String>, +cx: Ax) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> r:
      out.one(Bool.and(F.is_def(b), C.mem(ls, F.block_name(b))), b, cx) <> out_blocks(r, ls, cx)

# ---- the whole rewrite ----

def any_in(ts: List<&2, String>, +ns: List<&2, String>) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case +t <> r:
      Bool.or(C.mem(ns, t), any_in(r, ns))

# a def's type, when it names none of the def's own parameters (no type variables)
# (and a Data one: no pair, no function, so a parameter of it can be used twice)
def concrete(+b: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(F.ret_type(b))),
    Bool.and(Bool.not(F.is_type_rt(F.ret_type(b))),
      Bool.and(Bool.not(Bool.or(String.contains(F.ret_type(b), "&"), String.contains(F.ret_type(b), "->"))),
        Bool.not(any_in(C.tokens(F.ret_type(b)), C.names(C.Sig.ps(C.sig_of(b))))))))

def known.pick(hit: Bool, +k: String, +v: String, rest: List<&2, K.Kv>) -> List<&2, K.Kv>:
  match hit:
    case True{}:
      K.Kv{k, v} <> rest
    case False{}:
      rest

# the defs of bs with a concrete type: name (with pre in front) and type (qualified when al is given)
def known(bs: List<&2, String>, +pre: String, +al: String, +types: List<&2, String>, +skip: List<&2, String>) -> List<&2, K.Kv>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> r:
      known.pick(Bool.and(F.is_def(b), Bool.and(Bool.not(C.mem(skip, F.block_name(b))), concrete(b))),
        String.append(pre, F.block_name(b)), Bool.pick(String, String.is_empty(al), F.ret_type(b), P.qualify_one(F.ret_type(b), al, types)),
        known(r, pre, al, types, skip))

def proof_names(bs: List<&2, F.Blk>) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> r:
      P.keep.pick(Bool.not(F.Blk.proof(b)), F.Blk.name(b), proof_names(r))

def ctx(+phys: String, +proof: String, +base: String) -> Ax:
  +al = C.alias_of(proof)
  +types = P.type_names(C.blocks(phys))
  Ax{al, List.concat(&2, K.Kv, [known(C.blocks(phys), String.append(al, "."), al, types, Nil{}), known(C.blocks(base), SNil{}, SNil{}, Nil{}, Nil{}),
      known(C.blocks(proof), SNil{}, SNil{}, Nil{}, proof_names(F.proof_blks(proof)))]),
    def_names(C.blocks(proof)), C.blocks(proof), phys, types, C.blocks(phys)}

def why.one(+l: String, +cx: Ax) -> String:
  String.concat([l, ": ", Bd.why(step(O.lemma_of(Ax.bs(cx), l), l, cx, free_name(20n, l, 1n, Ax.defs(cx))))])

def whys(ls: List<&2, String>, +cx: Ax) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> r:
      P.keep.pick(Bd.ok(step(O.lemma_of(Ax.bs(cx), l), l, cx, free_name(20n, l, 1n, Ax.defs(cx)))), why.one(l, cx), whys(r, cx))

# the lemmas ls with every call that repeats a stuck record moved out
def abst.plan(+phys: String, +proof: String, +base: String, +ls: List<&2, String>) -> K.Plan:
  +proof2 = String.join(out_blocks(C.blocks(proof), ls, ctx(phys, proof, base)), "\n")
  K.Plan{Bool.not(String.eq(proof2, proof)),
    Bool.pick(String, String.eq(proof2, proof), String.concat(["abst ", String.join(ls, ","), ": nothing moved; ", String.join(whys(ls, ctx(phys, proof, base)), "; ")]),
      String.concat(["abst ", String.join(ls, ","), ": moved ", Nat.show(Nat.sub(List.length(&2, String, def_names(C.blocks(proof2))),
        List.length(&2, String, def_names(C.blocks(proof))))), " calls out; untouched: ", String.join(whys(ls, ctx(phys, proof, base)), "; ")])),
    phys, proof2, SNil{}}

# whether the rewrite takes anything in lemma l
def abst.fits(+phys: String, +proof: String, +base: String, +l: String) -> Bool:
  Bd.ok(step(O.lemma_of(C.blocks(proof), l), l, ctx(phys, proof, base), free_name(20n, l, 1n, def_names(C.blocks(proof)))))

def abst.write(ok: Bool, +dir: String, +pl: K.Plan) -> IO(String):
  match ok:
    case True{}:
      do IO<String>:
        u : Unit <- C.write_all(String.append(dir, "/PROOF.bend"), K.Plan.proof(pl))
        return K.Plan.msg(pl)
    case False{}:
      IO.pure(String, String.append("not applied: ", K.Plan.msg(pl)))

def abst.go(+dir: String, +pl: K.Plan) -> IO(String):
  abst.write(K.Plan.ok(pl), dir, pl)

# moves the calls out of lemmas ls, in <dir>/PROOF.bend
def abst(+dir: String, +ls: List<&2, String>) -> IO(String):
  do IO<String>:
    +home : String <- IO.try(String, IO.get_env("HOME"))
    +base : String <- C.read_all(String.append(home, "/.bend/bend2/base.bend"))
    +phys : String <- C.read_all(String.append(dir, "/phys.bend"))
    +proof : String <- C.read_all(String.append(dir, "/PROOF.bend"))
    abst.go(dir, abst.plan(phys, proof, base, ls))
