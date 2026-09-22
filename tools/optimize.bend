# Cubo -- proof optimizer.
#
#   bend tools/optimize.bend hoist <dir> <Def> <let> <Type>
#
# Rewrites <dir>/phys.bend and <dir>/PROOF.bend in place, so run it on a
# copy. The checker normalizes both sides of every equation in full, and a
# value it cannot decide (a `+<let> = ...` that matches on something still
# open) gets copied into every place <Def> uses it. This turns the let into
# a parameter of <Def>: callers compute it through a new def <Def>.<let>
# that stays folded while its arm is unknown, and every lemma whose
# statement unfolds <Def> takes it as a free variable instead.

import Base

type Ins is Data:
  Lit{text: String}
  Wrap{fname: String, idx: List<&2, Nat>}

type Spec is Data:
  Spec{name: String, pos: Nat, ins: Ins}

type Grp is Data:
  Grp{pending: List<&2, String>, groups: List<&2, List<&2, String>>}

type Sig is Data:
  Sig{pre: String, params: List<&2, String>, post: String}

type HD is Data:
  HD{wrapper: String, dblock: String, spec: Spec, wnames: List<&2, String>, nd: Nat, expr: String}

type Ctx is Data:
  Ctx{qd: String, qw: String, l: String, qt: String, nd: Nat, wn: List<&2, String>}

# ---- characters and strings ----

def is_ident(+c: Char) -> Bool:
  Bool.or(Bool.or(Char.is_alpha(c), Char.is_digit(c)), Bool.or(Char.is_eq(c, '_'), Char.is_eq(c, '.')))

def depth_step(+c: Char, +d: Nat) -> Nat:
  Bool.pick(Nat, Bool.or(Char.is_eq(c, '('), Bool.or(Char.is_eq(c, '['), Char.is_eq(c, '{'))), 1n+d,
    Bool.pick(Nat, Bool.or(Char.is_eq(c, ')'), Bool.or(Char.is_eq(c, ']'), Char.is_eq(c, '}'))), Nat.sub(d, 1n), d))

# The scanners below carry the answer for the current position as a
# parameter and stop at the first hit: a Bool.pick would build both sides.
def find.go(s: String, here: Bool, +pat: String, i: Nat) -> Maybe<&2, Nat>:
  match s here:
    case _ True{}:
      Some{i}
    case SNil{} False{}:
      None{}
    case SCon{h, +t} False{}:
      find.go(t, String.starts_with(t, pat), pat, 1n+i)

def find(+s: String, +pat: String) -> Maybe<&2, Nat>:
  find.go(s, String.starts_with(s, pat), pat, 0n)

def or_len(m: Maybe<&2, Nat>, d: Nat) -> Nat:
  match m:
    case None{}:
      d
    case Some{i}:
      i

# splitting a parameter list also has to see List<&2, T> as one piece; the
# `>` of `->` and `=>` closes nothing
def angle_step(+c: Char, +prev: Char, +d: Nat) -> Nat:
  Bool.pick(Nat, Char.is_eq(c, '<'), 1n+d,
    Bool.pick(Nat, Bool.and(Char.is_eq(c, '>'), Bool.not(Bool.or(Char.is_eq(prev, '-'), Char.is_eq(prev, '=')))),
      Nat.sub(d, 1n), depth_step(c, d)))

def split_top.go(s: String, +d: Nat, +sep: Char, +prev: Char) -> List<&2, String>:
  match s:
    case SNil{}:
      [SNil{}]
    case SCon{+h, t}:
      String.split.fin(h, split_top.go(t, angle_step(h, prev, d), sep, h), Bool.and(Char.is_eq(h, sep), Nat.is_eq(d, 0n)))

def split_top(s: String, +sep: Char) -> List<&2, String>:
  split_top.go(s, 0n, sep, ' ')

def close_at(s: String, d: Nat) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{h, t}:
      Bool.and(Char.is_eq(h, ')'), Nat.is_eq(d, 0n))

def close_idx.go(s: String, here: Bool, +d: Nat, i: Nat) -> Nat:
  match s here:
    case _ True{}:
      i
    case SNil{} False{}:
      i
    case SCon{+h, +t} False{}:
      close_idx.go(t, close_at(t, depth_step(h, d)), depth_step(h, d), 1n+i)

def close_idx(+s: String, +d: Nat) -> Nat:
  close_idx.go(s, close_at(s, d), d, 0n)

def sig_at(+s: String, d: Nat) -> Bool:
  Bool.and(String.starts_with(s, ":\n"), Nat.is_eq(d, 0n))

def sig_len.go(s: String, here: Bool, +d: Nat, i: Nat) -> Nat:
  match s here:
    case _ True{}:
      1n+i
    case SNil{} False{}:
      i
    case SCon{+h, +t} False{}:
      sig_len.go(t, sig_at(t, depth_step(h, d)), depth_step(h, d), 1n+i)

def sig_len(+s: String, +d: Nat) -> Nat:
  sig_len.go(s, sig_at(s, d), d, 0n)

def strip_q(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+h, +t}:
      Bool.pick(String, Bool.or(Char.is_eq(h, '+'), Char.is_eq(h, '-')), t, SCon{h, t})

def first_of(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case h <> t:
      h

def last_of(+xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case h <> Nil{}:
      h
    case h <> t:
      last_of(t)

def take_until_paren(s: String) -> String:
  first_of(String.split(s, '('))

def blank_non_ident(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+h, t}:
      SCon{Bool.pick(Char, is_ident(h), h, ' '), blank_non_ident(t)}

def tokens(s: String) -> List<&2, String>:
  String.split(blank_non_ident(s), ' ')

def after_eq.go(+t: String) -> String:
  String.drop(t, Nat.add(3n, or_len(find(t, " = "), 0n)))

def after_eq(h: String) -> String:
  after_eq.go(String.trim(h))

def starts_q(+s: String) -> Bool:
  Bool.or(String.starts_with(s, "+"), String.starts_with(s, "-"))

def add_plus(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+h, +t}:
      Bool.pick(String, Char.is_space(h), SCon{h, add_plus(t)}, SCon{'+', SCon{h, t}})

# ---- lists ----

def nth(xs: List<&2, String>, n: Nat) -> String:
  match xs n:
    case Nil{} _:
      SNil{}
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+m:
      nth(t, m)

def insert_at(k: Nat, xs: List<&2, String>, x: String) -> List<&2, String>:
  match k:
    case 0n:
      x <> xs
    case 1n+m:
      match xs:
        case Nil{}:
          [x]
        case h <> t:
          h <> insert_at(m, t, x)

def pname(chunk: String) -> String:
  String.trim(first_of(String.split(strip_q(String.trim(chunk)), ':')))

def names(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      pname(h) <> names(t)

def index_of.pick(hit: Bool, rest: Nat) -> Nat:
  match hit:
    case True{}:
      0n
    case False{}:
      1n+rest

def index_of(xs: List<&2, String>, +n: String) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      index_of.pick(String.eq(h, n), index_of(t, n))

def mem(xs: List<&2, String>, +n: String) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(String.eq(h, n), mem(t, n))

def idxs(wn: List<&2, String>, +ns: List<&2, String>) -> List<&2, Nat>:
  match wn:
    case Nil{}:
      Nil{}
    case h <> t:
      index_of(ns, h) <> idxs(t, ns)

def to2(xs: List<String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      h <> to2(t)

# ---- blocks: a top-level line and the indented lines under it ----

def is_head(line: String) -> Bool:
  match line:
    case SNil{}:
      False{}
    case SCon{h, t}:
      Bool.not(Char.is_eq(h, ' '))

def group.step(head: Bool, h: String, p: List<&2, String>, gs: List<&2, List<&2, String>>) -> Grp:
  match head:
    case True{}:
      Grp{Nil{}, (h <> p) <> gs}
    case False{}:
      Grp{h <> p, gs}

def group.push(head: Bool, h: String, g: Grp) -> Grp:
  match g:
    case Grp{p, gs}:
      group.step(head, h, p, gs)

def group.go(lines: List<&2, String>) -> Grp:
  match lines:
    case Nil{}:
      Grp{Nil{}, Nil{}}
    case +h <> t:
      group.push(is_head(h), h, group.go(t))

def group.fin.go(p: List<&2, String>, gs: List<&2, List<&2, String>>) -> List<&2, List<&2, String>>:
  match p:
    case Nil{}:
      gs
    case h <> t:
      (h <> t) <> gs

def group.fin(g: Grp) -> List<&2, List<&2, String>>:
  match g:
    case Grp{p, gs}:
      group.fin.go(p, gs)

def join_each(gs: List<&2, List<&2, String>>) -> List<&2, String>:
  match gs:
    case Nil{}:
      Nil{}
    case g <> r:
      String.join(g, "\n") <> join_each(r)

def blocks(text: String) -> List<&2, String>:
  join_each(group.fin(group.go(String.lines(text))))

def find_block(bs: List<&2, String>, +prefix: String) -> String:
  match bs:
    case Nil{}:
      SNil{}
    case +h <> t:
      Bool.pick(String, String.starts_with(h, prefix), h, find_block(t, prefix))

# ---- signatures ----

def Sig.pre(g: Sig) -> String:
  match g:
    case Sig{pre, ps, post}:
      pre

def Sig.ps(g: Sig) -> List<&2, String>:
  match g:
    case Sig{pre, ps, post}:
      ps

def Sig.post(g: Sig) -> String:
  match g:
    case Sig{pre, ps, post}:
      post

def sig_of.fin(pre: String, +after: String, +c: Nat) -> Sig:
  Sig{pre, split_top(String.take(after, c), ','), String.drop(after, c)}

def sig_of.go(+text: String, +o: Nat) -> Sig:
  sig_of.fin(String.take(text, 1n+o), String.drop(text, 1n+o), close_idx(String.drop(text, 1n+o), 0n))

def sig_of(+text: String) -> Sig:
  sig_of.go(text, or_len(find(text, "("), 0n))

def sig_text(g: Sig) -> String:
  match g:
    case Sig{pre, ps, post}:
      String.append(pre, String.append(String.join(ps, ","), post))

def sig_part(+b: String) -> String:
  String.take(b, sig_len(b, 0n))

# ---- rewriting calls ----

def Spec.nm(s: Spec) -> String:
  match s:
    case Spec{n, p, i}:
      n

def Spec.ps(s: Spec) -> Nat:
  match s:
    case Spec{n, p, i}:
      p

def Spec.in(s: Spec) -> Ins:
  match s:
    case Spec{n, p, i}:
      i

# a call site: pat (the name and its paren) here, not glued to a longer
# name, and not the name right after "def " that opens the block
def is_call_at(+s: String, +pat: String, +prev: Char, +i: Nat, skip4: Bool) -> Bool:
  Bool.and(String.starts_with(s, pat), Bool.and(Bool.not(is_ident(prev)), Bool.not(Bool.and(skip4, Nat.is_eq(i, 4n)))))

def pick_args(idx: List<&2, Nat>, +args: List<&2, String>) -> List<&2, String>:
  match idx:
    case Nil{}:
      Nil{}
    case k <> r:
      String.trim(nth(args, k)) <> pick_args(r, args)

def new_arg(ins: Ins, +args: List<&2, String>) -> String:
  match ins:
    case Lit{t}:
      String.append(" ", t)
    case Wrap{f, idx}:
      String.concat([" ", f, "(", String.join(pick_args(idx, args), ", "), ")"])

def split_call.out(+args: List<&2, String>, tail: String, +sp: Spec) -> String & String:
  (String.concat([Spec.nm(sp), "(", String.join(insert_at(Spec.ps(sp), args, new_arg(Spec.in(sp), args)), ","), ")"]), tail)

def split_call.fin(+after: String, +c: Nat, +sp: Spec) -> String & String:
  split_call.out(split_top(String.take(after, c), ','), String.drop(after, 1n+c), sp)

def split_call(+s: String, +sp: Spec) -> String & String:
  split_call.fin(String.drop(s, 1n+String.length(Spec.nm(sp))),
    close_idx(String.drop(s, 1n+String.length(Spec.nm(sp))), 0n), sp)

def pair.fst(p: String & String) -> String:
  match p:
    case (a, b):
      a

def pair.snd(p: String & String) -> String:
  match p:
    case (a, b):
      b

def rw(fuel: Nat, here: Bool, +s: String, +sp: Spec, +pat: String, +i: Nat, +skip4: Bool) -> String:
  match fuel here:
    case 0n _:
      s
    case 1n+f True{}:
      String.append(pair.fst(split_call(s, sp)),
        rw(f, is_call_at(pair.snd(split_call(s, sp)), pat, ')', 5n, skip4), pair.snd(split_call(s, sp)), sp, pat, 5n, skip4))
    case 1n+f False{}:
      match s:
        case SNil{}:
          SNil{}
        case SCon{+h, +t}:
          SCon{h, rw(f, is_call_at(t, pat, h, 1n+i, skip4), t, sp, pat, 1n+i, skip4)}

def rewrite.if(hit: Bool, +text: String, +sp: Spec, +pat: String) -> String:
  match hit:
    case True{}:
      rw(1n+String.length(text), is_call_at(text, pat, ' ', 0n, String.starts_with(text, "def ")), text, sp, pat, 0n,
        String.starts_with(text, "def "))
    case False{}:
      text

def rewrite.go(+text: String, +sp: Spec, +pat: String) -> String:
  rewrite.if(String.contains(text, pat), text, sp, pat)

def rewrite(+text: String, +sp: Spec) -> String:
  rewrite.go(text, sp, String.append(Spec.nm(sp), "("))

def rewrite_all(specs: List<&2, Spec>, +text: String) -> String:
  match specs:
    case Nil{}:
      text
    case sp <> r:
      rewrite_all(r, rewrite(text, sp))

# ---- quantities: a caller now reads the arm twice, so it must be `+` ----

def plus_if(hit: Bool, +chunk: String) -> String:
  match hit:
    case True{}:
      add_plus(chunk)
    case False{}:
      chunk

def needs_plus(+chunk: String, +wn: List<&2, String>) -> Bool:
  Bool.and(mem(wn, pname(chunk)), Bool.not(starts_q(String.trim(chunk))))

def fix_params(ps: List<&2, String>, +wn: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case +h <> t:
      plus_if(needs_plus(h, wn), h) <> fix_params(t, wn)

def fix_q(+text: String, +wn: List<&2, String>) -> String:
  sig_text(Sig{Sig.pre(sig_of(text)), fix_params(Sig.ps(sig_of(text)), wn), Sig.post(sig_of(text))})

def caller.fin(same: Bool, +new: String, +wn: List<&2, String>) -> String:
  match same:
    case True{}:
      new
    case False{}:
      fix_q(new, wn)

def caller.go(+old: String, +new: String, +wn: List<&2, String>) -> String:
  caller.fin(String.eq(old, new), new, wn)

def caller(+b: String, +specs: List<&2, Spec>, +wn: List<&2, String>) -> String:
  caller.go(b, rewrite_all(specs, b), wn)

# ---- the let ----

def is_let(+line: String, +l: String) -> Bool:
  Bool.or(String.starts_with(String.trim(line), String.concat(["+", l, " = "])),
    String.starts_with(String.trim(line), String.append(l, " = ")))

def drop_lets.pick(hit: Bool, h: String, rest: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      rest
    case False{}:
      h <> rest

def drop_lets(lines: List<&2, String>, +l: String) -> List<&2, String>:
  match lines:
    case Nil{}:
      Nil{}
    case +h <> t:
      drop_lets.pick(is_let(h, l), h, drop_lets(t, l))

def let_expr(lines: List<&2, String>, +l: String) -> String:
  match lines:
    case Nil{}:
      SNil{}
    case +h <> t:
      Bool.pick(String, is_let(h, l), after_eq(h), let_expr(t, l))

def pre_lets.keep(blank: Bool, h: String, rest: List<&2, String>) -> List<&2, String>:
  match blank:
    case True{}:
      rest
    case False{}:
      h <> rest

def pre_lets.pick(hit: Bool, blank: Bool, h: String, rest: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      Nil{}
    case False{}:
      pre_lets.keep(blank, h, rest)

def pre_lets(lines: List<&2, String>, +l: String) -> List<&2, String>:
  match lines:
    case Nil{}:
      Nil{}
    case +h <> t:
      pre_lets.pick(is_let(h, l), String.is_empty(String.trim(h)), h, pre_lets(t, l))

def used_params.pick(hit: Bool, h: String, rest: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      String.trim(h) <> rest
    case False{}:
      rest

def used_params(ps: List<&2, String>, +toks: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case +h <> t:
      used_params.pick(mem(toks, pname(h)), h, used_params(t, toks))

# ---- phys.bend: the def loses its let and gains the parameter ----

def HD.wrapper(h: HD) -> String:
  match h:
    case HD{w, b, s, n, d, e}:
      w

def HD.dblock(h: HD) -> String:
  match h:
    case HD{w, b, s, n, d, e}:
      b

def HD.spec(h: HD) -> Spec:
  match h:
    case HD{w, b, s, n, d, e}:
      s

def HD.wnames(h: HD) -> List<&2, String>:
  match h:
    case HD{w, b, s, n, d, e}:
      n

def HD.nd(h: HD) -> Nat:
  match h:
    case HD{w, b, s, n, d, e}:
      d

def HD.expr(h: HD) -> String:
  match h:
    case HD{w, b, s, n, d, e}:
      e

def hoist_def.body(+text1: String, +sl: Nat, +ps: List<&2, String>, +n: Nat, +d: String, +l: String, +t: String) -> HD:
  +lines = String.lines(String.drop(text1, sl))
  +expr = let_expr(lines, l)
  +pre = pre_lets(lines, l)
  +wp = used_params(ps, tokens(String.concat([String.join(pre, " "), " ", expr])))
  +wname = String.concat([d, ".", l])
  HD{
    String.concat(["def ", wname, "(", String.join(wp, ", "), ") -> ", t, ":\n", String.join(pre, "\n"), "\n  ", expr, "\n"]),
    String.append(String.take(text1, sl), String.join(drop_lets(lines, l), "\n")),
    Spec{d, Nat.sub(n, 1n), Wrap{wname, idxs(names(wp), names(ps))}},
    names(wp),
    n,
    expr
  }

def hoist_def.go(+g: Sig, +d: String, +l: String, +t: String) -> HD:
  +ps = Sig.ps(g)
  +n = List.length(&2, String, ps)
  +text1 = sig_text(Sig{Sig.pre(g), insert_at(Nat.sub(n, 1n), ps, String.concat([" +", l, ": ", t])), Sig.post(g)})
  hoist_def.body(text1, sig_len(text1, 0n), ps, n, d, l, t)

def hoist_def(+text: String, +d: String, +l: String, +t: String) -> HD:
  hoist_def.go(sig_of(text), d, l, t)

def phys_block.if(hit: Bool, +b: String, +h: HD) -> List<&2, String>:
  match hit:
    case True{}:
      [HD.wrapper(h), HD.dblock(h)]
    case False{}:
      [caller(b, [HD.spec(h)], HD.wnames(h))]

def phys_block(+b: String, +h: HD, +dp: String) -> List<&2, String>:
  phys_block.if(String.starts_with(b, dp), b, h)

def phys_all(bs: List<&2, String>, +h: HD, +dp: String) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> r:
      List.append(&2, String, phys_block(b, h, dp), phys_all(r, h, dp))

# ---- PROOF.bend: lemmas about the def take the parameter too ----

def Ctx.qd(c: Ctx) -> String:
  match c:
    case Ctx{qd, qw, l, qt, nd, wn}:
      qd

def Ctx.qw(c: Ctx) -> String:
  match c:
    case Ctx{qd, qw, l, qt, nd, wn}:
      qw

def Ctx.l(c: Ctx) -> String:
  match c:
    case Ctx{qd, qw, l, qt, nd, wn}:
      l

def Ctx.qt(c: Ctx) -> String:
  match c:
    case Ctx{qd, qw, l, qt, nd, wn}:
      qt

def Ctx.nd(c: Ctx) -> Nat:
  match c:
    case Ctx{qd, qw, l, qt, nd, wn}:
      nd

def Ctx.wn(c: Ctx) -> List<&2, String>:
  match c:
    case Ctx{qd, qw, l, qt, nd, wn}:
      wn

def alias_of(+text: String) -> String:
  String.trim(first_of(String.lines(String.drop(text, Nat.add(22n, or_len(find(text, "import ./phys.bend as "), 0n))))))

def is_lemma.if(hit: Bool, +b: String, +qd: String) -> Bool:
  match hit:
    case True{}:
      String.contains(sig_part(b), String.append(qd, "("))
    case False{}:
      False{}

def is_lemma(+b: String, +qd: String) -> Bool:
  is_lemma.if(Bool.and(String.starts_with(b, "def "), String.contains(b, String.append(qd, "("))), b, qd)

def qd_last_arg.go(+after: String) -> String:
  String.trim(last_of(split_top(String.take(after, close_idx(after, 0n)), ',')))

def qd_last_arg(+sig: String, +qd: String) -> String:
  qd_last_arg.go(String.drop(sig, Nat.add(1n+String.length(qd), or_len(find(sig, String.append(qd, "(")), 0n))))

def lemma_block.go(+text: String, +k: Nat, +c: Ctx) -> String:
  sig_text(Sig{Sig.pre(sig_of(text)), insert_at(k, Sig.ps(sig_of(text)), String.concat([" +", Ctx.l(c), ": ", Ctx.qt(c)])),
    Sig.post(sig_of(text))})

def lemma_block(+b: String, +c: Ctx) -> String:
  +sl = sig_len(b, 0n)
  +sig2 = rewrite(String.take(b, sl), Spec{Ctx.qd(c), Nat.sub(Ctx.nd(c), 1n), Lit{Ctx.l(c)}})
  +body = String.join(drop_lets(String.lines(String.drop(b, sl)), Ctx.l(c)), "\n")
  lemma_block.go(String.append(sig2, body), index_of(names(Sig.ps(sig_of(b))), qd_last_arg(sig_part(b), Ctx.qd(c))), c)

def lemma_spec(+b: String, +c: Ctx) -> Spec:
  +ps = Sig.ps(sig_of(b))
  Spec{take_until_paren(String.drop(b, 4n)), index_of(names(ps), qd_last_arg(sig_part(b), Ctx.qd(c))),
    Wrap{Ctx.qw(c), idxs(Ctx.wn(c), names(ps))}}

def lemma_specs.pick(hit: Bool, +b: String, +c: Ctx, rest: List<&2, Spec>) -> List<&2, Spec>:
  match hit:
    case True{}:
      lemma_spec(b, c) <> rest
    case False{}:
      rest

def lemma_specs(bs: List<&2, String>, +c: Ctx) -> List<&2, Spec>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> r:
      lemma_specs.pick(is_lemma(b, Ctx.qd(c)), b, c, lemma_specs(r, c))

def all_in(ws: List<&2, String>, +ns: List<&2, String>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(mem(ns, h), all_in(t, ns))

# a lemma can only be rewritten if its parameters carry every name the
# wrapper asks for, and the arm it hands to the def
def lemma_ok(+b: String, +c: Ctx) -> Bool:
  +ns = names(Sig.ps(sig_of(b)))
  Bool.and(all_in(Ctx.wn(c), ns), mem(ns, qd_last_arg(sig_part(b), Ctx.qd(c))))

def bad_lemmas.keep(ok: Bool, +b: String, rest: List<&2, String>) -> List<&2, String>:
  match ok:
    case True{}:
      rest
    case False{}:
      take_until_paren(String.drop(b, 4n)) <> rest

def bad_lemmas.pick(hit: Bool, +b: String, +c: Ctx, rest: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      bad_lemmas.keep(lemma_ok(b, c), b, rest)
    case False{}:
      rest

def bad_lemmas(bs: List<&2, String>, +c: Ctx) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> r:
      bad_lemmas.pick(is_lemma(b, Ctx.qd(c)), b, c, bad_lemmas(r, c))

def proof_block.lem(hit: Bool, +b: String, +c: Ctx) -> String:
  match hit:
    case True{}:
      lemma_block(b, c)
    case False{}:
      b

def proof_block(+b: String, +c: Ctx, +specs: List<&2, Spec>) -> String:
  caller(proof_block.lem(is_lemma(b, Ctx.qd(c)), b, c), specs, Ctx.wn(c))

def proof_all(bs: List<&2, String>, +c: Ctx, +specs: List<&2, Spec>) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> r:
      proof_block(b, c, specs) <> proof_all(r, c, specs)

def spec_names(ss: List<&2, Spec>) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case s <> r:
      Spec.nm(s) <> spec_names(r)

# ---- files ----

def finish_read2(f2: File, r: Result<&1, &1, U32 & String, String>) -> IO(String):
  match r:
    case Fail{e}:
      IO.die(String, 1, "read failed")
    case Done{text}:
      do IO<String>:
        File.close(f2)
        IO.pure(String, text)

def finish_read(rr: File & Result<&1, &1, U32 & String, String>) -> IO(String):
  match rr:
    case (f2, r):
      finish_read2(f2, r)

def read_with_size2(f1: File, r: Result<&1, &1, U32 & String, U32>) -> IO(String):
  match r:
    case Fail{e}:
      IO.die(String, 1, "size failed")
    case Done{n}:
      do IO<String>:
        rr : File & Result<&1, &1, U32 & String, String> <- File.read(f1, n)
        finish_read(rr)

def read_with_size(sz: File & Result<&1, &1, U32 & String, U32>) -> IO(String):
  match sz:
    case (f1, r):
      read_with_size2(f1, r)

def read_all(path: String) -> IO(String):
  do IO<String>:
    f0 : File <- IO.try(File, File.open(path, "r"))
    sz : File & Result<&1, &1, U32 & String, U32> <- File.size(f0)
    read_with_size(sz)

def write_all.close(f: File, res: Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  match res:
    case Fail{e}:
      IO.die(Unit, 1, "write failed")
    case Done{u}:
      File.close(f)

def write_all.fin(r: File & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  match r:
    case (f, res):
      write_all.close(f, res)

def write_all(path: String, data: String) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open(path, "w"))
    r : File & Result<&1, &1, U32 & String, Unit> <- File.write(f, data)
    write_all.fin(r)

def guard(ok: Bool, msg: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.pure(Unit, Unit{})
    case False{}:
      IO.die(Unit, 1, msg)

# ---- main ----

def hoist(+dir: String, +d: String, +l: String, +t: String) -> IO(Unit):
  do IO<Unit>:
    +phys : String <- read_all(String.append(dir, "/phys.bend"))
    +proof : String <- read_all(String.append(dir, "/PROOF.bend"))
    +dp : String = String.concat(["def ", d, "("])
    +target : String = find_block(blocks(phys), dp)
    u0 : Unit <- guard(Bool.not(String.is_empty(target)), String.concat(["no def ", d, " in phys.bend"]))
    +hd : HD = hoist_def(target, d, l, t)
    u1 : Unit <- guard(Bool.not(String.is_empty(HD.expr(hd))), String.concat(["no let ", l, " in ", d]))
    +al : String = alias_of(proof)
    +ctx : Ctx = Ctx{String.concat([al, ".", d]), String.concat([al, ".", d, ".", l]), l, String.concat([al, ".", t]), HD.nd(hd), HD.wnames(hd)}
    +pbs : List<&2, String> = blocks(proof)
    +specs : List<&2, Spec> = lemma_specs(pbs, ctx)
    +bad : List<&2, String> = bad_lemmas(pbs, ctx)
    u9 : Unit <- guard(Nat.is_eq(List.length(&2, String, bad), 0n),
      String.concat(["nothing written: these lemmas lack a parameter the wrapper needs: ", String.join(bad, ", ")]))
    u2 : Unit <- write_all(String.append(dir, "/phys.bend"), String.join(phys_all(blocks(phys), hd, dp), "\n"))
    u3 : Unit <- write_all(String.append(dir, "/PROOF.bend"), String.join(proof_all(pbs, ctx, specs), "\n"))
    IO.print(String.concat(["hoisted ", d, ".", l, "(", String.join(HD.wnames(hd), ", "), ") out of ", d,
      "; lemmas that now take ", l, ": ", String.join(spec_names(specs), ", ")]))

def usage() -> IO(Unit):
  IO.print("usage: bend tools/optimize.bend hoist <dir> <Def> <let> <Type>   (rewrites <dir>/phys.bend and <dir>/PROOF.bend in place)")

def run.go(ok: Bool, +a: List<&2, String>) -> IO(Unit):
  match ok:
    case True{}:
      hoist(nth(a, 1n), nth(a, 2n), nth(a, 3n), nth(a, 4n))
    case False{}:
      usage()

def run(+a: List<&2, String>) -> IO(Unit):
  run.go(Bool.and(String.eq(nth(a, 0n), "hoist"), Nat.is_le(5n, List.length(&2, String, a))), a)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    run(to2(args))
