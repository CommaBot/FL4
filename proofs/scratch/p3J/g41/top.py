# usage: python3 top.py OLD NEW RO RN LEAF GEN DESC > tail   (e.g. Lzj Lzk 17 18 sus 41 "Suspend")
# Generates the Mc-namespace tail (DispStabFoot<NEW>, implications, top) from P3JThPrio's (Lzi->Lzj, 16->17, prio).
import sys, re
old, new, ro, rn, leaf, gen, desc = sys.argv[1:8]
src = open('Fl4Proofs/P3/P3JThPrio.lean').read()
t = src[src.index('namespace Fl4Proofs.P3.Mc'):]
prev = {'Lzj':'Lzi'}
# P3JThPrio: Lzi (old) -> Lzj (new), rest 16 (old) -> 17 (new), leaf prio
t = t.replace('Lzj', '@NEW@').replace('Lzi', '@OLD@')
t = t.replace('IsRestCap17', '@RN@').replace('invDecRest16_of_prio', 'invDecRest@RO@_of_@LEAF@')
t = t.replace('midDecRest16_of_prio', 'midDecRest@RO@_of_@LEAF@')
t = t.replace('invDecStWL_of_16', 'invDecStWL_of_@RO@').replace('midDecStWL_of_16', 'midDecStWL_of_@RO@')
t = t.replace('(p3J gen 40)', '(p3J gen @GEN@)')
t = re.sub(r'/-- \(p3J gen @GEN@\) \*\*`DispStabFoot@NEW@` \[J\]\*\*:.*?-/', '/-- (p3J gen @GEN@) **`DispStabFoot@NEW@` [J]**: `DispStabFoot@OLD@` with `invDecRest` / `midDecRest` restricted to\n`IsRestCap@RNN@` (`IsRestCap@RON@` minus the Thread caps at @DESC@; module docstring). -/', t, flags=re.S)
t = t.replace('@NEW@', new).replace('@OLD@', old).replace('@RN@', 'IsRestCap'+rn).replace('@RNN@', rn).replace('@RON@', ro)
t = t.replace('@RO@', ro).replace('@LEAF@', leaf).replace('@GEN@', gen).replace('@DESC@', desc)
print(t, end='')
