# Cubo -- proof optimizer, the hoist rewrite: a `+let = ...` of a phys def
# becomes a parameter. Callers compute it through a new def <Def>.<let>
# that stays folded while its arm is unknown; the lemmas whose statement
# unfolds the def take it as a free variable; their callers pass the new
# def. hoist.plan builds both files or says why it cannot.

import Base
import ./core.bend as C

type HD is Data:
  HD{wrapper: String, dblock: String, spec: C.Spec, wnames: List<&2, String>, nd: Nat, expr: String}

type Ctx is Data:
  Ctx{qd: String, qw: String, l: String, qt: String, nd: Nat, wn: List<&2, String>}

# ---- characters and strings ----

def HD.wrapper(h: HD) -> String:
  match h:
    case HD{w, b, s, n, d, e}:
      w

def HD.dblock(h: HD) -> String:
  match h:
    case HD{w, b, s, n, d, e}:
      b

def HD.spec(h: HD) -> C.Spec:
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
  +expr = C.let_expr(lines, l)
  +pre = C.pre_lets(lines, l)
  +wp = C.used_params(ps, C.tokens(String.concat([String.join(pre, " "), " ", expr])))
  +wname = String.concat([d, ".", l])
  HD{
    String.concat(["def ", wname, "(", String.join(wp, ", "), ") -> ", t, ":\n", String.join(pre, "\n"), "\n  ", expr, "\n"]),
    String.append(String.take(text1, sl), String.join(C.drop_lets(lines, l), "\n")),
    C.Spec{d, Nat.sub(n, 1n), C.Wrap{wname, C.idxs(C.names(wp), C.names(ps))}},
    C.names(wp),
    n,
    expr
  }

def hoist_def.go(+g: C.Sig, +d: String, +l: String, +t: String) -> HD:
  +ps = C.Sig.ps(g)
  +n = List.length(&2, String, ps)
  +text1 = C.sig_text(C.Sig{C.Sig.pre(g), C.insert_at(Nat.sub(n, 1n), ps, String.concat([" +", l, ": ", t])), C.Sig.post(g)})
  hoist_def.body(text1, C.sig_len(text1, 0n), ps, n, d, l, t)

def hoist_def(+text: String, +d: String, +l: String, +t: String) -> HD:
  hoist_def.go(C.sig_of(text), d, l, t)

def phys_block.if(hit: Bool, +b: String, +h: HD) -> List<&2, String>:
  match hit:
    case True{}:
      [HD.wrapper(h), HD.dblock(h)]
    case False{}:
      [C.caller(b, [HD.spec(h)], HD.wnames(h))]

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

def is_lemma.if(hit: Bool, +b: String, +qd: String) -> Bool:
  match hit:
    case True{}:
      String.contains(C.sig_part(b), String.append(qd, "("))
    case False{}:
      False{}

def is_lemma(+b: String, +qd: String) -> Bool:
  is_lemma.if(Bool.and(String.starts_with(b, "def "), String.contains(b, String.append(qd, "("))), b, qd)

def qd_last_arg.go(+after: String) -> String:
  String.trim(C.last_of(C.split_top(String.take(after, C.close_idx(after, 0n)), ',')))

def qd_last_arg(+sig: String, +qd: String) -> String:
  qd_last_arg.go(String.drop(sig, Nat.add(1n+String.length(qd), C.or_len(C.find(sig, String.append(qd, "(")), 0n))))

def lemma_block.go(+text: String, +k: Nat, +c: Ctx) -> String:
  C.sig_text(C.Sig{C.Sig.pre(C.sig_of(text)), C.insert_at(k, C.Sig.ps(C.sig_of(text)), String.concat([" +", Ctx.l(c), ": ", Ctx.qt(c)])),
    C.Sig.post(C.sig_of(text))})

def lemma_block(+b: String, +c: Ctx) -> String:
  +sl = C.sig_len(b, 0n)
  +sig2 = C.rewrite(String.take(b, sl), C.Spec{Ctx.qd(c), Nat.sub(Ctx.nd(c), 1n), C.Lit{Ctx.l(c)}})
  +body = String.join(C.drop_lets(String.lines(String.drop(b, sl)), Ctx.l(c)), "\n")
  lemma_block.go(String.append(sig2, body), C.index_of(C.names(C.Sig.ps(C.sig_of(b))), qd_last_arg(C.sig_part(b), Ctx.qd(c))), c)

def lemma_spec(+b: String, +c: Ctx) -> C.Spec:
  +ps = C.Sig.ps(C.sig_of(b))
  C.Spec{C.take_until_paren(String.drop(b, 4n)), C.index_of(C.names(ps), qd_last_arg(C.sig_part(b), Ctx.qd(c))),
    C.Wrap{Ctx.qw(c), C.idxs(Ctx.wn(c), C.names(ps))}}

def lemma_specs.pick(hit: Bool, +b: String, +c: Ctx, rest: List<&2, C.Spec>) -> List<&2, C.Spec>:
  match hit:
    case True{}:
      lemma_spec(b, c) <> rest
    case False{}:
      rest

def lemma_specs(bs: List<&2, String>, +c: Ctx) -> List<&2, C.Spec>:
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
      Bool.and(C.mem(ns, h), all_in(t, ns))

# a lemma can only be rewritten if its parameters carry every name the
# wrapper asks for, and the arm it hands to the def
def lemma_ok(+b: String, +c: Ctx) -> Bool:
  +ns = C.names(C.Sig.ps(C.sig_of(b)))
  Bool.and(all_in(Ctx.wn(c), ns), C.mem(ns, qd_last_arg(C.sig_part(b), Ctx.qd(c))))

def bad_lemmas.keep(ok: Bool, +b: String, rest: List<&2, String>) -> List<&2, String>:
  match ok:
    case True{}:
      rest
    case False{}:
      C.take_until_paren(String.drop(b, 4n)) <> rest

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

def proof_block(+b: String, +c: Ctx, +specs: List<&2, C.Spec>) -> String:
  C.caller(proof_block.lem(is_lemma(b, Ctx.qd(c)), b, c), specs, Ctx.wn(c))

def proof_all(bs: List<&2, String>, +c: Ctx, +specs: List<&2, C.Spec>) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case b <> r:
      proof_block(b, c, specs) <> proof_all(r, c, specs)

def spec_names(ss: List<&2, C.Spec>) -> List<&2, String>:
  match ss:
    case Nil{}:
      Nil{}
    case s <> r:
      C.Spec.nm(s) <> spec_names(r)

# ---- files ----

type HP is Data:
  HP{ok: Bool, msg: String, phys: String, proof: String}

def HP.ok(h: HP) -> Bool:
  match h:
    case HP{o, m, a, b}:
      o

def HP.msg(h: HP) -> String:
  match h:
    case HP{o, m, a, b}:
      m

def HP.phys(h: HP) -> String:
  match h:
    case HP{o, m, a, b}:
      a

def HP.proof(h: HP) -> String:
  match h:
    case HP{o, m, a, b}:
      b

def hoist.refuse(+msg: String) -> HP:
  HP{False{}, msg, SNil{}, SNil{}}

def hoist.done(+phys: String, +pbs: List<&2, String>, +hd: HD, +ctx: Ctx, +specs: List<&2, C.Spec>, +d: String, +l: String) -> HP:
  HP{True{}, String.concat(["hoisted ", d, ".", l, "(", String.join(HD.wnames(hd), ", "), ") out of ", d,
      "; lemmas that now take ", l, ": ", String.join(spec_names(specs), ", ")]),
    String.join(phys_all(C.blocks(phys), hd, String.concat(["def ", d, "("])), "\n"),
    String.join(proof_all(pbs, ctx, specs), "\n")}

def hoist.lemmas(ok: Bool, +phys: String, +pbs: List<&2, String>, +hd: HD, +ctx: Ctx, +d: String, +l: String) -> HP:
  match ok:
    case True{}:
      hoist.done(phys, pbs, hd, ctx, lemma_specs(pbs, ctx), d, l)
    case False{}:
      hoist.refuse(String.concat(["these lemmas lack a parameter the wrapper needs: ", String.join(bad_lemmas(pbs, ctx), ", ")]))

def hoist.ctx(+phys: String, +proof: String, +hd: HD, +d: String, +l: String, +t: String) -> HP:
  +al = C.alias_of(proof)
  +ctx = {Ctx{String.concat([al, ".", d]), String.concat([al, ".", d, ".", l]), l, String.concat([al, ".", t]), HD.nd(hd), HD.wnames(hd)} : Ctx}
  +pbs = C.blocks(proof)
  hoist.lemmas(Nat.is_eq(List.length(&2, String, bad_lemmas(pbs, ctx)), 0n), phys, pbs, hd, ctx, d, l)

def hoist.let(ok: Bool, +phys: String, +proof: String, +hd: HD, +d: String, +l: String, +t: String) -> HP:
  match ok:
    case True{}:
      hoist.ctx(phys, proof, hd, d, l, t)
    case False{}:
      hoist.refuse(String.concat(["no let ", l, " in ", d]))

def hoist.found(found: Bool, +phys: String, +proof: String, +target: String, +d: String, +l: String, +t: String) -> HP:
  match found:
    case True{}:
      hoist.let(Bool.not(String.is_empty(HD.expr(hoist_def(target, d, l, t)))), phys, proof, hoist_def(target, d, l, t), d, l, t)
    case False{}:
      hoist.refuse(String.concat(["no def ", d, " in phys.bend"]))

# the C.rewrite of both files, or why it cannot be done; nothing is written
def hoist.plan(+phys: String, +proof: String, +d: String, +l: String, +t: String) -> HP:
  +target = C.find_block(C.blocks(phys), String.concat(["def ", d, "("]))
  hoist.found(Bool.not(String.is_empty(target)), phys, proof, target, d, l, t)

def hoist.write(+dir: String, +h: HP) -> IO(Unit):
  do IO<Unit>:
    u0 : Unit <- C.guard(HP.ok(h), String.append("nothing written: ", HP.msg(h)))
    u1 : Unit <- C.write_all(String.append(dir, "/phys.bend"), HP.phys(h))
    u2 : Unit <- C.write_all(String.append(dir, "/PROOF.bend"), HP.proof(h))
    IO.print(HP.msg(h))

def hoist(+dir: String, +d: String, +l: String, +t: String) -> IO(Unit):
  do IO<Unit>:
    +phys : String <- C.read_all(String.append(dir, "/phys.bend"))
    +proof : String <- C.read_all(String.append(dir, "/PROOF.bend"))
    hoist.write(dir, hoist.plan(phys, proof, d, l, t))

# ---- running a command ----
