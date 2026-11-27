#!/usr/bin/env python3
"""List every def/theorem of the gen-18 files as `#print axioms` (run from proofs/)."""
import re
FILES = [('Fl4Proofs.P3.VirtWrSys', 'Fl4Proofs/P3/VirtWrSys.lean'),
         ('Fl4Proofs.P3.VirtNoRunDel', 'Fl4Proofs/P3/VirtNoRunDel.lean'),
         ('Fl4Proofs.P3.VirtNoRunStep', 'Fl4Proofs/P3/VirtNoRunStep.lean')]
out = ['import %s' % m for m, _ in FILES]
for _, f in FILES:
    ns = []
    for line in open(f):
        m = re.match(r'namespace (\S+)', line)
        if m: ns.append(m.group(1)); continue
        m = re.match(r'end (\S+)', line)
        if m and ns and ns[-1] == m.group(1): ns.pop(); continue
        m = re.match(r'(?:theorem|def) (\S+)', line)
        if m: out.append('#print axioms %s.%s' % (ns[-1], m.group(1)))
open('scratch/virt/virt18_ax.lean', 'w').write('\n'.join(out) + '\n')
print(len(out) - len(FILES))
