import re, sys
sys.path.insert(0, 'scratch/p3J/g46')
from gen import header_split, find_theorem
names = set(l.split()[1] for l in open(sys.argv[1]))
short = {n.split('.')[-1] for n in names}
for l in open(sys.argv[1]):
    f, n = l.split()[:2]
    t = open('Fl4Proofs/P3/' + f).read()
    pre, th, end = find_theorem(t, n)
    h, b = header_split(t[th:end])
    post = re.search(r'(RJR|RJ|JAtR|JAt|RelTopM \(L := L\) r\.1 z\.2 ∧ JAtR) \(L := L\) arI AR r\.1 r\.2 z\.2\s*⦄', h)
    print('=====', f, n, post.group(1) if post else '??', 'hb:', t[pre:th].count('set_option'))
    base = t[:th].count('\n') + 1
    for k, line in enumerate(b.split('\n')):
        if 'inferInstance' in line or any(re.search(r'\.' + re.escape(s) + r'\b|^\s*(exact |refine )?' + re.escape(s) + r'\b|[ (]' + re.escape(s) + r'\b', line) for s in short) or 'spec_mono' in line:
            print('  %d: %s' % (base + h.count('\n') + k, line.strip()[:200]))
