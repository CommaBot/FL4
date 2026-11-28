# usage: python3 top.py OLD NEW RO RN LEAF GEN DESC > tail   (e.g. Lzo Lzp 22 23 gb 42 "GetBreakpoint")
# Generates the Mc-namespace tail (DispStabFoot<NEW>, implications, top) from P3JThCp's (Lzn->Lzo, 21->22, cp).
import sys, re
old, new, ro, rn, leaf, gen, desc = sys.argv[1:8]
src = open('Fl4Proofs/P3/P3JThCp.lean').read()
t = src[src.index('namespace Fl4Proofs.P3.Mc'):]
t = t.replace('Lzo', '@NEW@').replace('Lzn', '@OLD@')
t = t.replace('IsRestCap22', '@RN@').replace('invDecRest21_of_cp', 'invDecRest@RO@_of_@LEAF@')
t = t.replace('midDecRest21_of_cp', 'midDecRest@RO@_of_@LEAF@')
t = t.replace('invDecStWL_of_21', 'invDecStWL_of_@RO@').replace('midDecStWL_of_21', 'midDecStWL_of_@RO@')
t = t.replace('IsRestCap21', 'IsRestCap@RO@')
t = t.replace('(p3J gen 41)', '(p3J gen @GEN@)').replace('at CopyRegisters', 'at @DESC@')
t = t.replace('@NEW@', new).replace('@OLD@', old).replace('@RN@', 'IsRestCap'+rn)
t = t.replace('@RO@', ro).replace('@LEAF@', leaf).replace('@GEN@', gen).replace('@DESC@', desc)
print(t, end='')
