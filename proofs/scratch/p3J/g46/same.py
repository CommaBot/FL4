import re, subprocess, sys
sys.path.insert(0, 'scratch/p3J/g46')
from gen import header_split
for f in ['Fl4Proofs/P3/XTopJointMRTcb.lean', 'Fl4Proofs/P3/XTopJointMRTcbM.lean']:
    old = subprocess.run(['git', 'show', 'HEAD:proofs/' + f], capture_output=True, text=True).stdout
    new = open(f).read()
    names = re.findall(r'^(?:theorem|structure|def|abbrev) (\S+)', old, re.M)
    newnames = set(re.findall(r'^(?:theorem|structure|def|abbrev) (\S+)', new, re.M))
    for n in names:
        def hd(t):
            m = re.search(r'^((?:theorem|structure|def|abbrev) ' + re.escape(n) + r'[ \n])', t, re.M)
            d = t[m.start():]
            if d.startswith('structure'):
                return d[:d.index('\n\n')]
            return header_split(d)[0]
        same = hd(old) == hd(new)
        print(('SAME ' if same else 'DIFF ') + n)
    print('new names:', sorted(newnames - set(names)))
