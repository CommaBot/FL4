#!/usr/bin/env python3
"""p3J gen 54 (gen 53's body.py + callee-only lists `<list> [<extra>...]`): rewrite the moved bodies of the `…Q` theorems (after gen.py) — exits, internal posts, calls.

Usage, from proofs/: python3 scratch/p3J/g53/body.py <list>   (list lines: `<file> <name> ...`, the closure)
In each `TQ` body only:
* exits `Jk.xtop.relTop, _, _, _, _, _, _, Jk, inferInstance⟩` -> `Jk.xtop.relTop, hPq _ _ _ _ _ _ _ _ Jk⟩`;
* internal posts `RJ/RJR (L := L) arI AR r.1 r.2 z.2 ⦄` -> `RelTopM (L := L) r.1 z.2 ∧ Pq r.1 r.2 z.2 ⦄`;
* `WP.spec_mono (X …) fun r ⟨…, J', _⟩ => ⟨…, J'.toR, inferInstance⟩` -> `XQ … (fun … J' => hPq … J'.toR)`;
* every other call of a listed `X` -> `XQ … <hPq or its toR form>` (argument appended at the end of the call).
"""
import re, sys
sys.path.insert(0, 'scratch/p3J/g46')
from gen import header_split, find_theorem

lst = [l.split()[:2] for l in open(sys.argv[1]) if l.strip()]
# gen 54: callee-only lists (earlier batches, already `…Q`): known for call rewriting, bodies untouched
extra = [l.split()[:2] for a in sys.argv[2:] for l in open(a) if l.strip()]
names = {n for _, n in lst + extra}
kinds = {}
for f, n in lst + extra:
    t = open('Fl4Proofs/P3/' + f).read()
    pre, th, end = find_theorem(t, n + 'Q')
    h, _ = header_split(t[th:end])
    kinds[n] = 'R' if 'JAtZR (L := L) arI AR (Z.mv G V)' in h else 'Z'
short = {}
for n in names:
    short[n.split('.')[-1]] = n
TOR = "(fun _ _ _ _ _ _ _ _ J' => hPq _ _ _ _ _ _ _ _ J'.toR)"
NEWP = 'RelTopM (L := L) r.1 z.2 ∧ Pq r.1 r.2 z.2 ⦄'
MONO_TAIL = re.compile(r"\s*fun r ⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J', _⟩ =>\s*⟨z, hz, hR, Z', H', Cs', Ac', Lst', D', J'\.toR, inferInstance⟩")
CALL = re.compile(r"(?<![\w.'])((?:J\w*'*\.)?)(" + '|'.join(sorted(map(re.escape, short), key=len, reverse=True)) + r")(?![\w'])")
log = []

def arg(caller, callee):
    kc, ke = kinds[caller], kinds[callee]
    if kc == ke:
        return 'hPq'
    if kc == 'R' and ke == 'Z':
        return TOR
    raise ValueError((caller, callee))

def match_paren(s, i):
    d = 0
    for k in range(i, len(s)):
        if s[k] in '([{⟨':
            d += 1
        elif s[k] in ')]}⟩':
            d -= 1
            if d == 0:
                return k
    raise ValueError

def callend(b, i):
    ls = b.rfind('\n', 0, i) + 1
    ind = len(b[ls:]) - len(b[ls:].lstrip(' '))
    e = b.find('\n', i)
    while e != -1:
        nl = b.find('\n', e + 1)
        line = b[e + 1: nl if nl != -1 else len(b)]
        if line.strip() == '' or (len(line) - len(line.lstrip(' '))) <= ind:
            return e
        e = nl
    return len(b)

def fix_body(caller, b):
    b = re.sub(r"([\w']+)\.xtop\.relTop, _, _, _, _, _, _, \1, inferInstance⟩", r"\1.xtop.relTop, hPq _ _ _ _ _ _ _ _ \1⟩", b)
    b = re.sub(r'\bRJR? \(L := L\) arI AR r\.1 r\.2 z\.2 ⦄', NEWP, b)
    # suffices … from WP.spec_mono hRJ fun … => ⟨…⟩
    b = re.sub(r"from\s*WP\.spec_mono (\w+)" + MONO_TAIL.pattern, r"from \1", b)
    # spec_mono wrappers
    while True:
        m = re.search(r'WP\.spec_mono \(', b)
        found = False
        for m in re.finditer(r'WP\.spec_mono \(', b):
            i = m.end() - 1
            j = match_paren(b, i)
            inner = b[i + 1:j]
            cm = CALL.match(inner)
            t = MONO_TAIL.match(b, j + 1)
            if cm and t:
                callee = short[cm.group(2)]
                new = cm.group(1) + cm.group(2) + 'Q' + inner[cm.end():] + ' ' + TOR
                assert kinds[callee] == 'Z' and kinds[caller] == 'R', (caller, callee)
                b = b[:m.start()] + new + b[t.end():]
                log.append(('mono', caller, callee))
                found = True
                break
        if not found:
            break
    # plain calls
    pos = 0
    while True:
        m = CALL.search(b, pos)
        if not m:
            break
        ls = b.rfind('\n', 0, m.start()) + 1
        if b[m.end():m.end() + 1] in ('Q', "'", '`') or '--' in b[ls:m.start()] or b[m.start() - 1] == '`':
            pos = m.end(); continue
        callee = short[m.group(2)]
        a = arg(caller, callee)
        b = b[:m.end()] + 'Q' + b[m.end():]
        e = callend(b, m.end())
        b = b[:e].rstrip(' ') + ' ' + a + b[e:]
        log.append(('call', caller, callee))
        pos = m.end() + 1
    return b

files = {}
for f, n in lst:
    files.setdefault(f, []).append(n)
for f, ns in files.items():
    p = 'Fl4Proofs/P3/' + f
    t = open(p).read()
    for n in ns:
        pre, th, end = find_theorem(t, n + 'Q')
        h, b = header_split(t[th:end])
        t = t[:th] + h + fix_body(n, b) + t[end:]
    open(p, 'w').write(t)
for x in log:
    print(*x)
