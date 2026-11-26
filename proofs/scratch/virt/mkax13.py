#!/usr/bin/env python3
"""List every def/theorem of the gen-13 files as `#print axioms` (run from proofs/)."""
import re
FILES = [('Fl4Proofs.P3.VirtF13', 'Fl4Proofs/P3/VirtF13.lean'),
         ('Fl4Proofs.P3.VirtKEntryV3F', 'Fl4Proofs/P3/VirtKEntryV3F.lean'),
         ('Fl4Proofs.P3.VirtWit13', 'Fl4Proofs/P3/VirtWit13.lean'),
         ('Fl4Proofs.P3.VirtMsrEq', 'Fl4Proofs/P3/VirtMsrEq.lean'),
         ('Fl4Proofs.P3.VirtInitIo', 'Fl4Proofs/P3/VirtInitIo.lean')]
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
open('scratch/virt/virt13_ax.lean', 'w').write('\n'.join(out) + '\n')
print(len(out) - len(FILES))
