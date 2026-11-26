# gen 5: JBootIoa — the witness at warI1 (warI with one IOAPIC of 24 pins). Copies JBootU34's u34_w0I and
# JBootJAt's jAtZ_w0 field list, renamed to warI1; kern / utc rebuilt (they are the only JAtZ fields naming arI).
import re, pathlib
P = pathlib.Path
u34 = P('Fl4Proofs/P3/JBootU34.lean').read_text()
jat = P('Fl4Proofs/P3/JBootJAt.lean').read_text()
def ren(t):
    t = t.replace('warI_', 'warI1_')
    t = re.sub(r'\bwarI\b', 'warI1', t)
    return t
# jAtZ field list
a = jat.index('theorem jAtZ_w0'); b = jat.index('/-- **`JAt` at the witness')
jz = ren(jat[a:b]).replace('theorem jAtZ_w0', 'theorem jAtZ_w0I1')
jz = jz.replace('  kern := w0_jkern\n', '  kern := w0_jkernI1\n').replace('  utc := w0_utc\n', '  utc := w0_utcI1\n')
assert 'w0_jkernI1' in jz and 'w0_utcI1' in jz
# U34 part: from MachPlatF to the end of u34_w0I, minus OpaqueWK
a = u34.index('/-- **`MachPlatF` for the witness arch'); b = u34.index('\nend\n\nend Fl4Proofs')
body = u34[a:b]
oa = body.index('/-- **wit\'s `OpaqueW` without `ipi`**'); ob = body.index('theorem warI_max_periodK')
body = body[:oa] + body[ob:]
body = ren(body)
body = body.replace('u34_w0I', 'u34_w0I1').replace('jReachU34_w0I⟩', 'jReachU34_w0I1⟩')
body = body.replace('JReachU34 (L := wL) warI1 wAR ipiMR w0 fInitASt.machineState fInitASt :=\n  ⟨⟨',
                    'JReachU34 (L := wL) warI1 wAR ipiMR w0 fInitASt.machineState fInitASt :=\n  ⟨⟨')
head = P('scratch/p3J/W1head.lean').read_text()
mid = P('scratch/p3J/W1mid.lean').read_text()
tail = P('scratch/p3J/W1tail.lean').read_text()
reach = P('scratch/p3J/W1reach.lean').read_text()
total = P('scratch/p3J/total.txt').read_text()
P('Fl4Proofs/P3/JBootIoa.lean').write_text(head + total + '\n' + mid + jz + reach + body + '\n' + tail)
