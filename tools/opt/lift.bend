# Cubo -- proof optimizer, the lift rewrite.
#
# A def of phys.bend that is one `match v:` over a parameter and answers a
# record R{...}: a proof that asks for one field of its answer has to open
# the match first, even for a field that every branch gives the same way
# (Body.spin only ever changes the rotation, but Body.x of it waited on
# `moved`). Each field is asked of the checker: `{R.f(E1) == R.f(Ek)}` by
# {==} for every branch k. The fields it accepts leave the match; the rest
# get a def of their own that keeps it. The new def is then checked field
# by field against the old one before anything is written.

import Base
import ./core.bend as C
import ./prof.bend as F

type Case is Data:
  Case{pat: String, expr: String}

type Fld is Data:
  Fld{name: String, ty: String}

type Lift is Data:
  Lift{ok: Bool, why: String, dname: String, rname: String, scrut: String, params: List<&2, String>,
    cases: List<&2, Case>, fields: List<&2, Fld>}

# ---- reading the def ----

def Case.pat(c: Case) -> String:
  match c:
    case Case{p, e}:
      p

def Case.expr(c: Case) -> String:
  match c:
    case Case{p, e}:
      e

def Fld.name(f: Fld) -> String:
  match f:
    case Fld{n, t}:
      n

def Fld.ty(f: Fld) -> String:
  match f:
    case Fld{n, t}:
      t

def is_case(+l: String) -> Bool:
  Bool.and(String.starts_with(l, "    case "), String.ends_with(String.trim_end(l), ":"))

def pat_of_line(+l: String) -> String:
  String.trim(F.drop_colon(String.trim(String.drop(l, 9n))))

def is_blank(+l: String) -> Bool:
  String.is_empty(String.trim(l))

type Cs is Data:
  Cs{pending: List<&2, String>, cases: List<&2, Case>}

def cs.body(blank: Bool, +l: String, p: List<&2, String>, cs: List<&2, Case>) -> Cs:
  match blank:
    case True{}:
      Cs{p, cs}
    case False{}:
      Cs{String.drop(l, 6n) <> p, cs}

def cs.line(isc: Bool, blank: Bool, +l: String, p: List<&2, String>, cs: List<&2, Case>) -> Cs:
  match isc:
    case True{}:
      Cs{Nil{}, Case{pat_of_line(l), String.join(p, "\n")} <> cs}
    case False{}:
      cs.body(blank, l, p, cs)

def cs.push(+l: String, acc: Cs) -> Cs:
  match acc:
    case Cs{p, cs}:
      cs.line(is_case(l), is_blank(l), l, p, cs)

def cs.go(ls: List<&2, String>) -> Cs:
  match ls:
    case Nil{}:
      Cs{Nil{}, Nil{}}
    case +l <> r:
      cs.push(l, cs.go(r))

def cs.fin(acc: Cs) -> List<&2, Case>:
  match acc:
    case Cs{p, cs}:
      cs

# the body lines after the `match v:` line
def after_match(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      Nil{}
    case +l <> +r:
      Bool.pick(List<&2, String>, String.starts_with(String.trim(l), "match "), r, after_match(r))

def first_code(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      SNil{}
    case +l <> r:
      Bool.pick(String, is_blank(l), first_code(r), String.trim(l))

def body_lines(+b: String) -> List<&2, String>:
  String.lines(String.drop(b, C.sig_len(b, 0n)))

# `match v:` over one name
def scrut_of(+first: String) -> String:
  String.trim(F.drop_colon(String.drop(first, 6n)))

def single_scrut(+first: String) -> Bool:
  Bool.and(String.starts_with(first, "match "),
    Bool.and(String.ends_with(first, ":"), Bool.not(String.contains(scrut_of(first), " "))))

# a branch that is one expression: no let, no match, no case under it
def plain_expr(+e: String) -> Bool:
  Bool.not(Bool.or(String.contains(e, " = "), Bool.or(String.contains(e, "match "), String.contains(e, "case "))))

def lower_start(+s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{h, t}:
      Char.is_lower(h)

def any_lower(ts: List<&2, String>) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case +t <> r:
      Bool.or(lower_start(t), any_lower(r))

# a pattern that binds nothing: True{}, False{}, [], 0n
def binds_nothing(+p: String) -> Bool:
  Bool.not(any_lower(C.tokens(p)))

def cases_ok(cs: List<&2, Case>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case +c <> r:
      Bool.and(Bool.and(binds_nothing(Case.pat(c)), plain_expr(Case.expr(c))), cases_ok(r))

# ---- the record it answers ----

def ctor_line(ls: List<&2, String>, +r: String) -> String:
  match ls:
    case Nil{}:
      SNil{}
    case +l <> t:
      Bool.pick(String, String.starts_with(String.trim(l), String.append(r, "{")), String.trim(l), ctor_line(t, r))

def ctor_count(ls: List<&2, String>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case +l <> t:
      Nat.add(Bool.pick(Nat, Bool.and(String.starts_with(l, "  "), String.contains(l, "{")), 1n, 0n), ctor_count(t))

def fld_of(+c: String) -> Fld:
  Fld{C.pname(c), String.trim(C.last_of(String.split(c, ':')))}

def flds(cs: List<&2, String>) -> List<&2, Fld>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> r:
      fld_of(c) <> flds(r)

# R{f: T, ...} on one line: what lies between the first { and the last }
def fields_of.go(+line: String) -> List<&2, Fld>:
  flds(C.split_top(String.take(String.drop(line, Nat.add(1n, C.or_len(C.find(line, "{"), 0n))),
    Nat.sub(String.length(line), Nat.add(2n, C.or_len(C.find(line, "{"), 0n)))), ','))

def fields_of(+tblock: String, +r: String) -> List<&2, Fld>:
  Bool.pick(List<&2, Fld>, Nat.is_eq(ctor_count(String.lines(tblock)), 1n),
    fields_of.go(ctor_line(String.lines(tblock), r)), Nil{})

def accessors_ok(fs: List<&2, Fld>, +bs: List<&2, String>, +r: String) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case +f <> t:
      Bool.and(Bool.not(String.is_empty(C.find_block(bs, String.concat(["def ", r, ".", Fld.name(f), "("])))),
        accessors_ok(t, bs, r))

# ---- everything the rewrite needs, or why it cannot be done ----

def Lift.ok(x: Lift) -> Bool:
  match x:
    case Lift{o, w, d, r, v, ps, cs, fs}:
      o

def Lift.why(x: Lift) -> String:
  match x:
    case Lift{o, w, d, r, v, ps, cs, fs}:
      w

def Lift.dname(x: Lift) -> String:
  match x:
    case Lift{o, w, d, r, v, ps, cs, fs}:
      d

def Lift.rname(x: Lift) -> String:
  match x:
    case Lift{o, w, d, r, v, ps, cs, fs}:
      r

def Lift.scrut(x: Lift) -> String:
  match x:
    case Lift{o, w, d, r, v, ps, cs, fs}:
      v

def Lift.params(x: Lift) -> List<&2, String>:
  match x:
    case Lift{o, w, d, r, v, ps, cs, fs}:
      ps

def Lift.cases(x: Lift) -> List<&2, Case>:
  match x:
    case Lift{o, w, d, r, v, ps, cs, fs}:
      cs

def Lift.fields(x: Lift) -> List<&2, Fld>:
  match x:
    case Lift{o, w, d, r, v, ps, cs, fs}:
      fs

def no(+d: String, +why: String) -> Lift:
  Lift{False{}, why, d, SNil{}, SNil{}, Nil{}, Nil{}, Nil{}}

def read_lift.fields(+d: String, +r: String, +b: String, +bs: List<&2, String>, +first: String, +cs: List<&2, Case>) -> Lift:
  +fs = fields_of(C.find_block(bs, String.concat(["type ", r, " is"])), r)
  Bool.pick(Lift, Bool.and(Nat.is_le(1n, List.length(&2, Fld, fs)), accessors_ok(fs, bs, r)),
    Lift{True{}, SNil{}, d, r, scrut_of(first), C.Sig.ps(C.sig_of(b)), cs, fs},
    no(d, String.concat(["it answers ", r, ", not a one-constructor record with an accessor per field"])))

def read_lift.cases(+d: String, +b: String, +bs: List<&2, String>, +first: String) -> Lift:
  +cs = cs.fin(cs.go(after_match(body_lines(b))))
  Bool.pick(Lift, Bool.and(Nat.is_le(2n, List.length(&2, Case, cs)), cases_ok(cs)),
    read_lift.fields(d, F.ret_type(b), b, bs, first, cs),
    no(d, "its branches bind names, hold lets, or are fewer than two"))

def read_lift.body(+d: String, +b: String, +bs: List<&2, String>) -> Lift:
  +first = first_code(body_lines(b))
  Bool.pick(Lift, single_scrut(first), read_lift.cases(d, b, bs, first), no(d, "its body is not one match over one name"))

def read_lift(+d: String, +bs: List<&2, String>) -> Lift:
  +b = C.find_block(bs, String.concat(["def ", d, "("]))
  Bool.pick(Lift, String.is_empty(b), no(d, "no such def"), read_lift.body(d, b, bs))

# ---- the text it writes ----

def first_expr(cs: List<&2, Case>) -> String:
  match cs:
    case Nil{}:
      SNil{}
    case +c <> r:
      Case.expr(c)

def proj(+r: String, +f: String, +e: String) -> String:
  String.concat([r, ".", f, "(", e, ")"])

def sig_line(+name: String, +ps: List<&2, String>, +ty: String) -> String:
  String.concat(["def ", name, "(", String.join(C.fix_params(ps, C.names(ps)), ","), ") -> ", ty, ":"])

def case_lines(cs: List<&2, Case>, +r: String, +f: String, +eq: Bool) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> t:
      String.concat(["    case ", Case.pat(c), ":\n      ",
        Bool.pick(String, eq, "{==}", proj(r, f, Case.expr(c)))]) <> case_lines(t, r, f, eq)

# the def that keeps the match, for a field the branches disagree on
def field_def(+x: Lift, +f: Fld) -> String:
  String.concat([sig_line(String.concat([Lift.dname(x), ".", Fld.name(f)]), Lift.params(x), Fld.ty(f)), "\n",
    "  match ", Lift.scrut(x), ":\n", String.join(case_lines(Lift.cases(x), Lift.rname(x), Fld.name(f), False{}), "\n"), "\n"])

def args_of(+x: Lift) -> String:
  String.join(C.names(Lift.params(x)), ", ")

def field_expr(inv: Bool, +x: Lift, +f: Fld) -> String:
  Bool.pick(String, inv, proj(Lift.rname(x), Fld.name(f), first_expr(Lift.cases(x))),
    String.concat([Lift.dname(x), ".", Fld.name(f), "(", args_of(x), ")"]))

def field_exprs(fs: List<&2, Fld>, invs: List<&2, Bool>, +x: Lift) -> List<&2, String>:
  match fs invs:
    case Nil{} _:
      Nil{}
    case Con{f, r} Nil{}:
      Nil{}
    case Con{+f, r} Con{i, ir}:
      field_expr(i, x, f) <> field_exprs(r, ir, x)

def split_defs.pick(inv: Bool, +x: Lift, +f: Fld, rest: List<&2, String>) -> List<&2, String>:
  match inv:
    case True{}:
      rest
    case False{}:
      field_def(x, f) <> rest

def split_defs(fs: List<&2, Fld>, invs: List<&2, Bool>, +x: Lift) -> List<&2, String>:
  match fs invs:
    case Nil{} _:
      Nil{}
    case Con{f, r} Nil{}:
      Nil{}
    case Con{+f, r} Con{i, ir}:
      split_defs.pick(i, x, f, split_defs(r, ir, x))

# the new text of the def: its field defs, then the record built field by field
def new_block(+x: Lift, +invs: List<&2, Bool>) -> String:
  String.concat([String.join(split_defs(Lift.fields(x), invs, x), "\n"), "\n",
    sig_line(Lift.dname(x), Lift.params(x), Lift.rname(x)), "\n  ", Lift.rname(x), "{",
    String.join(field_exprs(Lift.fields(x), invs, x), ", "), "}\n"])

# ---- what the checker is asked ----

# field f of branch 1 against branch k, one def per other branch
def inv_defs(cs: List<&2, Case>, +x: Lift, +f: Fld, +e1: String, +i: Nat) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case +c <> r:
      String.concat([sig_line(String.concat(["lift.inv.", Nat.show(i)]), Lift.params(x),
        String.concat(["{", proj(Lift.rname(x), Fld.name(f), e1), " == ", proj(Lift.rname(x), Fld.name(f), Case.expr(c)),
        " : ", Fld.ty(f), "}"])), "\n  {==}\n"]) <> inv_defs(r, x, f, e1, 1n+i)

def inv_file(+phys: String, +x: Lift, +f: Fld) -> String:
  String.concat([phys, "\n\n", String.join(inv_defs(Lift.cases(x), x, f, first_expr(Lift.cases(x)), 0n), "\n")])

# the old def, renamed, against the new one: field by field, per branch
def eq_defs(fs: List<&2, Fld>, +x: Lift, +i: Nat) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case +f <> r:
      String.concat([sig_line(String.concat(["lift.eq.", Nat.show(i)]), Lift.params(x),
        String.concat(["{", proj(Lift.rname(x), Fld.name(f), String.concat([Lift.dname(x), ".orig(", args_of(x), ")"])), " == ",
        proj(Lift.rname(x), Fld.name(f), String.concat([Lift.dname(x), "(", args_of(x), ")"])), " : ", Fld.ty(f), "}"])), "\n",
        "  match ", Lift.scrut(x), ":\n", String.join(case_lines(Lift.cases(x), Lift.rname(x), Fld.name(f), True{}), "\n"), "\n"])
        <> eq_defs(r, x, 1n+i)

# ---- running it ----

def status_ok(ts: List<&2, F.Tm>, +k: Nat) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case +t <> r:
      Bool.or(Bool.and(Nat.is_eq(F.Tm.idx(t), k), String.eq(F.Tm.st(t), "ok")), status_ok(r, k))

def inv_list(+ts: List<&2, F.Tm>, n: Nat, +k: Nat) -> List<&2, Bool>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      status_ok(ts, k) <> inv_list(ts, m, 1n+k)

def write_invs(fs: List<&2, Fld>, +phys: String, +x: Lift, +dir: String, +k: Nat) -> IO(Unit):
  match fs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case +f <> r:
      do IO<Unit>:
        u : Unit <- C.write_all(String.concat([dir, "/LIFT_", Nat.show(k), ".bend"]), inv_file(phys, x, f))
        write_invs(r, phys, x, dir, 1n+k)

def count_true(bs: List<&2, Bool>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case b <> r:
      Nat.add(Bool.pick(Nat, b, 1n, 0n), count_true(r))

def swap_block.one(hit: Bool, +b: String, +nb: String) -> String:
  match hit:
    case True{}:
      nb
    case False{}:
      b

def swap_block(bs: List<&2, String>, +prefix: String, +nb: String) -> List<&2, String>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> r:
      swap_block.one(String.starts_with(b, prefix), b, nb) <> swap_block(r, prefix, nb)

def orig_block(+b: String, +d: String) -> String:
  String.append(String.concat(["def ", d, ".orig("]), String.drop(b, Nat.add(5n, String.length(d))))

def eq_file(+newphys: String, +x: Lift, +orig: String) -> String:
  String.concat([newphys, "\n\n", orig_block(orig, Lift.dname(x)), "\n\n",
    String.join(eq_defs(Lift.fields(x), x, 0n), "\n")])

def check_one(+dir: String, +name: String, +text: String, +cap: Nat) -> IO(Bool):
  do IO<Bool>:
    u : Unit <- C.write_all(String.concat([dir, "/", name, "_0.bend"]), text)
    out : String <- IO.try(String, C.Sys.run(F.run_cmd(dir, String.append(name, "_*.bend"), 1n, cap)))
    return status_ok(F.tms(String.lines(out)), 0n)

def lift.apply(ok: Bool, +dir: String, +newphys: String, +msg: String) -> IO(String):
  match ok:
    case True{}:
      do IO<String>:
        u : Unit <- C.write_all(String.append(dir, "/phys.bend"), newphys)
        return String.append("lifted ", msg)
    case False{}:
      IO.pure(String, String.append("not lifted (the new def is not equal to the old one): ", msg))

def lift.verify(+dir: String, +x: Lift, +invs: List<&2, Bool>, +bs: List<&2, String>, +cap: Nat) -> IO(String):
  +prefix = String.concat(["def ", Lift.dname(x), "("])
  +newphys = String.join(swap_block(bs, prefix, new_block(x, invs)), "\n")
  +msg = String.concat([Lift.dname(x), ": ", Nat.show(count_true(invs)), " of ", Nat.show(List.length(&2, Fld, Lift.fields(x))),
    " fields of ", Lift.rname(x), " leave the match on ", Lift.scrut(x)])
  do IO<String>:
    ok : Bool <- check_one(dir, "LIFTEQ", eq_file(newphys, x, C.find_block(bs, prefix)), cap)
    lift.apply(ok, dir, newphys, msg)

def lift.try_fields(useful: Bool, +dir: String, +x: Lift, +invs: List<&2, Bool>, +bs: List<&2, String>, +cap: Nat) -> IO(String):
  match useful:
    case True{}:
      lift.verify(dir, x, invs, bs, cap)
    case False{}:
      IO.pure(String, String.concat(["not lifted: no field of ", Lift.rname(x), " is the same in every branch of ", Lift.dname(x)]))

def lift.run(+dir: String, +x: Lift, +phys: String, +bs: List<&2, String>, +par: Nat, +cap: Nat) -> IO(String):
  do IO<String>:
    u : Unit <- write_invs(Lift.fields(x), phys, x, dir, 0n)
    out : String <- IO.try(String, C.Sys.run(F.run_cmd(dir, "LIFT_*.bend", par, cap)))
    +invs : List<&2, Bool> = inv_list(F.tms(String.lines(out)), List.length(&2, Fld, Lift.fields(x)), 0n)
    lift.try_fields(Nat.is_le(1n, count_true(invs)), dir, x, invs, bs, cap)

def lift.go(ok: Bool, +dir: String, +x: Lift, +phys: String, +bs: List<&2, String>, +par: Nat, +cap: Nat) -> IO(String):
  match ok:
    case True{}:
      lift.run(dir, x, phys, bs, par, cap)
    case False{}:
      IO.pure(String, String.concat(["not lifted: ", Lift.dname(x), ": ", Lift.why(x)]))

# rewrites <dir>/phys.bend only when the checker agreed to all of it
def lift(+dir: String, +d: String, +par: Nat, +cap: Nat) -> IO(String):
  do IO<String>:
    +phys : String <- C.read_all(String.append(dir, "/phys.bend"))
    +bs : List<&2, String> = C.blocks(phys)
    +x : Lift = read_lift(d, bs)
    lift.go(Lift.ok(x), dir, x, phys, bs, par, cap)
