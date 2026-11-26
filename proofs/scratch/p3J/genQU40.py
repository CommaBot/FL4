# gen 7: JBootQU40 (jAtZ field list from JBootQJAt renamed to warI1, kern / utc as JBootIoa).
import re, pathlib
P = pathlib.Path
jat = P('Fl4Proofs/P3/JBootQJAt.lean').read_text()
a = jat.index('theorem jAtZ_w0'); b = jat.index('/-- **`JAt` at the witness')
jz = re.sub(r'\bwarI\b', 'warI1', jat[a:b]).replace('theorem jAtZ_w0', 'theorem jAtZ_w0I1')
jz = jz.replace('  kern := w0_jkern\n', '  kern := w0_jkernI1\n').replace('  utc := w0_utc\n', '  utc := w0_utcI1\n')
assert 'w0_jkernI1' in jz and 'w0_utcI1' in jz
mid = P('scratch/p3J/W1mid.lean').read_text()
P('Fl4Proofs/P3/JBootQU40.lean').write_text(P('scratch/p3J/QU40head.lean').read_text() + mid + jz +
    P('scratch/p3J/QU40tail.lean').read_text())
