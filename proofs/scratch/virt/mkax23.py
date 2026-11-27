#!/usr/bin/env python3
"""List every def/theorem/abbrev/structure of the gen-23 files as `#print axioms` (run from proofs/)."""
import re
MODS = ['VirtResetSpecV', 'VirtVCapped', 'VirtVCappedDel']
FILES = [('Fl4Proofs.P3.' + m, 'Fl4Proofs/P3/%s.lean' % m) for m in MODS]
out = ['import %s' % m for m, _ in FILES]
n = 0
for _, f in FILES:
    ns = []
    for line in open(f):
        m = re.match(r'namespace (\S+)', line)
        if m: ns.append(m.group(1)); continue
        m = re.match(r'end (\S+)', line)
        if m and ns and ns[-1] == m.group(1): ns.pop(); continue
        m = re.match(r'(?:theorem|def|abbrev|structure) (\S+)', line)
        if m:
            out.append('#print axioms %s.%s' % ('.'.join(ns), m.group(1))); n += 1
open('scratch/virt/virt23_ax.lean', 'w').write('\n'.join(out) + '\n')
print(n)
