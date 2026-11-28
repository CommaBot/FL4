"""Call closure (text level) from given roots over P3 theorems whose post is existential-ghost (RJR/RJ/JAtR/JAt)."""
import re, sys, glob, os
sys.path.insert(0, 'scratch/p3J/g46')
from gen import header_split
decls = {}
for f in glob.glob('Fl4Proofs/P3/*.lean'):
    t = open(f).read()
    for m in re.finditer(r'^theorem (\S+)', t, re.M):
        name = m.group(1)
        rest = t[m.start():]
        m2 = re.compile(r'^(set_option|/--|theorem |def |structure |abbrev |end\b|section\b|variable |namespace )', re.M).search(rest, 1)
        d = rest[:m2.start()] if m2 else rest
        try:
            h, b = header_split(d)
        except Exception:
            continue
        decls.setdefault(name, []).append((os.path.basename(f), h, b))
POST = re.compile(r'(RJR \(L := L\) arI AR r\.1 r\.2 z\.2|RJ \(L := L\) arI AR r\.1 r\.2 z\.2|JAtR \(L := L\) arI AR r\.1 r\.2 z\.2|JAt \(L := L\) arI AR r\.1 r\.2 z\.2)\s*⦄\s*:=$')
def ex(name):
    return any(POST.search(h.strip()) for _, h, _ in decls.get(name, []))
short = {}
for n in decls:
    short.setdefault(n.split('.')[-1], set()).add(n)
roots = sys.argv[1:]
seen = []; todo = list(roots)
while todo:
    n = todo.pop()
    if n in seen: continue
    seen.append(n)
    for f, h, b in decls.get(n, []):
        ids = set(re.findall(r"[A-Za-z_][\w'.]*", b))
        for i in ids:
            cands = set()
            if i in decls: cands.add(i)
            last = i.split('.')[-1]
            if '.' in i and last in short:
                cands |= {c for c in short[last] if c.startswith('JAtZ') }
            for c in cands:
                if ex(c) and c not in seen: todo.append(c)
for n in seen:
    for f, h, b in decls.get(n, []):
        print(f, n, 'EX' if ex(n) else '--', len(decls[n]))
