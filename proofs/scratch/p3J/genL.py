# p3J gen 2: generate P3/P3JLook.lean — the narrowed path premises (`LookAt`), their conversions, the
# narrowed `handle_invocation_refinesMXP` and the two consumers, all as text copies of the originals.
import re, sys, os
root = sys.argv[1]
P3 = root + '/Fl4Proofs/P3/'

def lines(f): return open(P3 + f).read().split('\n')

def find_decl(kind, name):
    for f in sorted(os.listdir(P3)):
        if not f.endswith('.lean'): continue
        L = lines(f)
        for i, l in enumerate(L):
            if re.match(r'^%s %s( |$)' % (kind, re.escape(name)), l):
                return f, L, i
    raise SystemExit('missing %s %s' % (kind, name))

def span(L, i):
    # declaration from line i to the first blank line; with the `set_option … in` lines just above
    j = i
    while j < len(L) and L[j].strip() != '': j += 1
    k = i
    while k > 0 and L[k-1].startswith('set_option') and L[k-1].rstrip().endswith(' in'): k -= 1
    return '\n'.join(L[k:j])

def context(L, i):
    # namespace path, opens and variable/include/omit lines of the scopes enclosing line i
    stack = [('top', None, [])]   # (kind, nsname, items)
    last = None
    for l in L[:i]:
        if last is not None and l.startswith('  ') and l.strip():
            stack[-1][2][-1] += '\n' + l; continue
        last = None
        m = re.match(r'^namespace (\S+)', l)
        if m: stack.append(('ns', m.group(1), [])); continue
        if re.match(r'^(noncomputable )?section\b', l): stack.append(('sec', None, [])); continue
        if re.match(r'^end\b', l):
            if len(stack) > 1: stack.pop()
            continue
        if re.match(r'^(open|variable|include|omit) ', l):
            stack[-1][2].append(l); last = l; continue
    ns = '.'.join(s[1] for s in stack if s[0] == 'ns')
    ops = [x for s in stack for x in s[2] if x.startswith('open')]
    vs = [x for s in stack for x in s[2] if not x.startswith('open')]
    return ns, ops, vs

DEFS = ['JPathAtM', 'JPathAtM35', 'JPathAtM35E', 'JPathAtM36E', 'JPathAtMU4', 'JPathAtMU7', 'JPathAtMU12',
        'JPathAtMU17', 'JPathAtMU18', 'JPathAtMU19', 'JPathAtMU21', 'JPathAtMU25', 'JPathAtMU26', 'JPathAtMU27',
        'JPathAtMU28', 'JPathAtMU29', 'JPathAtMU30']
NEW = {d: (d + 'L') for d in DEFS}
NEW['JPathAtMU30'] = 'JPathAtMU35'
CONVS = ['JPathAtM35.toM', 'JPathAtM35E.to35', 'JPathAtM36E.to35E', 'JPathAtMU4.to36E', 'JPathAtMU7.toU4',
         'JPathAtMU12.toU7', 'JPathAtMU17.toU12', 'JPathAtMU18.toU17', 'JPathAtMU19.toU18', 'JPathAtMU21.toU19',
         'JPathAtMU25.toU21', 'JPathAtMU26.toU25', 'JPathAtMU27.toU26', 'JPathAtMU28.toU27', 'JPathAtMU29.toU28',
         'JPathAtMU30.toU29']
defre = re.compile(r'\bJPathAtM(U\d+|35E|36E|35)?(?=[\s)])')
def ren(t): return defre.sub(lambda m: NEW[m.group(0)], t)

out = []
blocks = []  # (ns, opens, vars, text, fullname-pairs)
pairs = []   # (original full name, new full name)

def emit(ns, ops, vs, text):
    # a docstring goes after any `set_option … in` lines
    ls = text.split('\n')
    if ls[0].startswith('/--') and len(ls) > 1 and ls[1].startswith('set_option'):
        k = 1
        while ls[k].startswith('set_option'): k += 1
        ls = ls[1:k] + [ls[0]] + ls[k:]
        text = '\n'.join(ls)
    blocks.append((ns, ops, vs, text))

for d in DEFS:
    f, L, i = find_decl('def', d)
    ns, ops, vs = context(L, i)
    t = span(L, i)
    t2 = t.replace('def %s ' % d, 'def %s ' % NEW[d], 1)
    pat = re.compile(r'(r2 = \.Ok e → er = \.ok exs →( Vs\.NativeCap c →)?)')
    assert len(pat.findall(t2)) == 1, d
    t2 = pat.sub(lambda m: m.group(1) + ' LookAt ct cptr σ sl c →', t2)
    t2 = ('/-- **`%s` narrowed to the invoked slot** (P3JLook): one more hypothesis, `LookAt ct cptr σ sl c`, '
          'that `sl` / `c` are what the spec\'s `lookupCapAndSlot` returns for `cptr`. -/\n' % d) + t2
    emit(ns, ops, vs, t2)
    pairs.append(('def', ns + '.' + d, ns + '.' + NEW[d]))

for c in CONVS:
    src, tgt = c.split('.')
    f, L, i = find_decl('theorem', c)
    ns, ops, vs = context(L, i)
    t = span(L, i)
    # the target def of the conversion: from the statement line with ` :` ending
    newname = NEW[src] + '.' + tgt + 'L'
    t2 = t.replace('theorem %s ' % c, 'theorem %s ' % newname, 1)
    t2 = ren(t2)
    m = re.search(r'(intro|fun) (info mi buf buffer r2 er argsU[^\n=]*?)( =>)?\n', t2)
    assert m, c
    binders = m.group(2).rstrip()
    t2 = t2[:m.start(2)] + binders + ' hL' + t2[m.start(2) + len(m.group(2).rstrip()):]
    app = 'h ' + binders
    n_app = t2.count(app)
    assert n_app == 1, (c, n_app)
    j = t2.index(app) + len(app)
    if t2[j:j+3] == ' hN':
        j += 3
    t2 = t2[:j] + ' hL' + t2[j:]
    t2 = '/-- `%s` on the narrowed premises (P3JLook). -/\n' % c + t2
    emit(ns, ops, vs, t2)
    pairs.append(('conv', ns + '.' + c, ns + '.' + newname))

# the narrowed refinement lemma
f, L, i = find_decl('theorem', 'handle_invocation_refinesMXP')
ns, ops, vs = context(L, i)
t = span(L, i)
t2 = t.replace('theorem handle_invocation_refinesMXP ', 'theorem handle_invocation_refinesMXPL ', 1)
old = 'Fl4Spec.getCap (Z := Unit) sl σ = ({(absCap c, σ)}, False) → r2 = .Ok e → er = .ok exs →\n      XCapP'
assert t2.count(old) == 1
t2 = t2.replace(old, 'Fl4Spec.getCap (Z := Unit) sl σ = ({(absCap c, σ)}, False) → r2 = .Ok e → er = .ok exs →\n      LookAt ct cptr σ sl c → XCapP')
old = 'hDec sl c ex exs ⟨p, hp, hth⟩ hc hget rfl rfl with'
assert t2.count(old) == 1
t2 = t2.replace(old, 'hDec sl c ex exs ⟨p, hp, hth⟩ hc hget rfl rfl hl with')
t2 = ('/-- **`handle_invocation_refinesMXP` with `hDec` asked only at the slot the lookup returns** '
      '(`LookAt`, the lookup\'s own outcome `hl` in the original proof). -/\n') + t2
emit(ns, ops, vs, t2)

# the two consumers
CONS = [('handle_invocation_entryJMU', 'Fl4ProofsI.P3.handle_invocation_entryJMU',
         [('JEntryAt (L := L)', 'Fl4ProofsI.P3.JEntryAtN (L := L)'), ('decOK_JMU ', 'Fl4ProofsI.P3.decOK_JMU ')]),
        ('handle_invocation_entryJMUM', 'Fl4ProofsQI.P3.handle_invocation_entryJMUM',
         [('JEntryAt (L := L)', 'Fl4ProofsI.P3.JEntryAtN (L := L)'), ('decOK_JMM ', 'Fl4ProofsQI.P3.decOK_JMM '),
          ('MachPlat arI MR', 'MachPlatT arI MR'), ('spec_mrz', 'Fl4ProofsQ.P3.spec_mrz'),
          ('msF_mr', 'Fl4ProofsQ.P3.msF_mr')])]
for (nm, orig, reps) in CONS:
    f, L, i = find_decl('theorem', nm)
    ns, ops, vs = context(L, i)
    t = span(L, i)
    t2 = t.replace('theorem %s ' % nm, 'theorem %sL ' % nm, 1)
    t2 = t2.replace('(hP : JPathAtM (L := L)', '(hP : JPathAtML (L := L)')
    for a, b in reps:
        t2 = re.sub(r'(?<![\w.])' + re.escape(a), b, t2)
    assert t2.count('handle_invocation_refinesMXP ') == 1, nm
    t2 = t2.replace('handle_invocation_refinesMXP ', 'handle_invocation_refinesMXPL ')
    old = 'intro sl c e exs hsl hc hget h1 h2\n'
    assert t2.count(old) == 1, nm
    t2 = t2.replace(old, 'intro sl c e exs hsl hc hget h1 h2 hL\n')
    old = 'hP info mi buf buffer r2 er argsU hinfo hmi hbuf hbuffer hr2 her hmrs sl c e exs hsl hc hget h1 h2)'
    assert t2.count(old) == 1, nm
    t2 = t2.replace(old, old[:-1] + ' hL)')
    t2 = '/-- `%s` on `JPathAtML` (P3JLook). -/\n' % orig + t2
    emit(ns, ops, vs, t2)
    pairs.append(('cons', orig, ns + '.' + nm + 'L'))

head = open(root + '/scratch/p3J/Lhead.lean').read()
body = []
for (ns, ops, vs, text) in blocks:
    body.append('namespace %s\n%s\nnoncomputable section\nsection\n%s\n\n%s\n\nend\nend\nend %s\n' % (
        ns, '\n'.join(ops), '\n'.join(vs), text, ns))
open(P3 + 'P3JLook.lean', 'w').write(head + '\n' + '\n'.join(body))
with open(root + '/scratch/p3J/pairs.txt', 'w') as g:
    for k, a, b in pairs: g.write('%s %s %s\n' % (k, a, b))
print(len(blocks), 'blocks')
