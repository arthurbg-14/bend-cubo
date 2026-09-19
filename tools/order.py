#!/usr/bin/env python3
# Puts a Bend file's top-level defs in an order Bend accepts: every def
# after the defs it uses (Bend wants a name defined above its use), and
# otherwise as they were. A block is a def, type or law with the comment
# lines right above it; the file's head (imports, its first comments)
# stays first.
#   tools/order.py file.bend
import re, sys
path = sys.argv[1]
text = open(path).read()
lines = text.split("\n")
starts = [i for i, l in enumerate(lines) if re.match(r'(def|type|law|@unsafe def) ', l)]
if not starts:
    sys.exit(0)
# attach comments/blank lines above each block
def block_start(i):
    j = i
    while j > 0 and (lines[j-1].startswith("#") ) :
        j -= 1
    return j
bstarts = [block_start(i) for i in starts]
head = "\n".join(lines[:bstarts[0]])
blocks = []
for n, (bs, s) in enumerate(zip(bstarts, starts)):
    end = bstarts[n+1] if n + 1 < len(starts) else len(lines)
    body = "\n".join(lines[bs:end]).rstrip("\n")
    m = re.match(r'(?:@unsafe )?(def|type|law) ([\w.]+)', lines[s])
    blocks.append((m.group(1), m.group(2), body))
names = {b[1] for b in blocks}
# type constructors belong to their type's block
ctor_owner = {}
for kind, name, body in blocks:
    if kind == "type":
        for c in re.findall(r'^  ([A-Z][\w.]*)\{', body, re.M):
            ctor_owner[c] = name
deps = {}
for kind, name, body in blocks:
    d = set()
    for tok in re.findall(r'(?<![\w.])([A-Za-z_][\w.]*)(?=[({<])', body):
        if tok in names and tok != name:
            d.add(tok)
        if tok in ctor_owner and ctor_owner[tok] != name:
            d.add(ctor_owner[tok])
    for tok in re.findall(r'(?<![\w.])([A-Z][\w.]*)', body):
        if tok in names and tok != name and any(b[0] == "type" and b[1] == tok for b in blocks):
            d.add(tok)
    deps[name] = d
out, done, busy = [], set(), set()
index = {b[1]: b for b in blocks}
def visit(n):
    if n in done or n in busy:
        return
    busy.add(n)
    for m in sorted(deps[n], key=lambda x: [b[1] for b in blocks].index(x)):
        visit(m)
    busy.discard(n)
    done.add(n)
    out.append(index[n][2])
for b in blocks:
    visit(b[1])
open(path, "w").write(head.rstrip("\n") + "\n\n" + "\n\n".join(out) + "\n")
