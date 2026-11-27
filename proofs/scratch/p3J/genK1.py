# gen 9: text copies on ArchSwF' into Fl4Proofs/P3/ArchSwIdle.lean (between BEGIN/END markers)
def rng(f,a,b): return '\n'.join(open(f).read().split('\n')[a-1:b])
def subs(body,pairs):
    for x,y in pairs:
        assert body.count(x)==1,(x,body.count(x)); body=body.replace(x,y)
    return body
G='Fl4Proofs/P3/G7eChain.lean'; F='Fl4Proofs/P3/ScScheduleF.lean'; D='Fl4Proofs/P3/ScNextDomF.lean'
scntA=subs(rng(G,135,218),[('theorem scnt_refines0FA ','theorem scnt_refines0FAI '),
  ('/-- `scnt_refines0F` with the CR3. -/','/-- `scnt_refines0FA` on `ArchSwF\'` (the idle half at `RootOK.idle`). -/'),
  ('(hA : ArchSwF st ar N T C c)',"(hA : ArchSwF' st ar N T C c)"),
  ('(hA.2 s a σ hS hR hvr)','(hA.2 s a σ hS hR hvr hO.now.idle)'),
  ('(hA.2 _ a σn hSn hRn hvrN)','(hA.2 _ a σn hSn hRn hvrN (hO _ _ hwN haK.1 hcN).idle)')])
swA=subs(rng(G,111,133),[('theorem sw_refinesFA ','theorem sw_refinesFAI '),('(hA : ArchSwF st ar N T C c)',"(hA : ArchSwF' st ar N T C c)")])
swA='/-- `sw_refinesFA` on `ArchSwF\'` (thread half only). -/\n'+swA
sw=subs(rng(F,65,85),[('theorem sw_refinesF ','theorem sw_refinesFI '),('(hA : ArchSwF st ar N T C c)',"(hA : ArchSwF' st ar N T C c)")])
scnt=subs(rng(D,40,126),[('theorem scnt_refines0F ','theorem scnt_refines0FI '),
  ('(hA : ArchSwF st ar N T C c)',"(hA : ArchSwF' st ar N T C c)"),
  ('(hvr : VsRootOK T σ)\n','(hvr : VsRootOK T σ) (hIV : IdleVt σ)\n'),
  ('(hA.2 s a σ hS hR hvr)','(hA.2 s a σ hS hR hvr hIV)'),
  ('(hA.2 _ a σn hSn hRn hvrN)','(hA.2 _ a σn hSn hRn hvrN (IdleVt.frame (σ\' := σn) hIV haK.1 haK.2.2.2.2.2.2.2.2.1))')])
scnt=scnt.replace('/-- **`schedule_choose_new_thread` refines l4v\'s, with the domain switch**:','/-- ScNextDomF\'s `scnt_refines0F` on `ArchSwF\'`, given `IdleVt σ` (carried to the domain-switch state `σn` by\n`IdleVt.frame`). Original docstring: **`schedule_choose_new_thread` refines l4v\'s, with the domain switch**:',1)
for mark,body in [('scnt',scntA+'\n\n'+swA+'\n\n'+sw),('scntN',scnt)]:
    f='Fl4Proofs/P3/ArchSwIdle.lean'; t=open(f).read()
    a,rest=t.split('-- BEGIN %s\n'%mark); _,c=rest.split('-- END %s\n'%mark)
    open(f,'w').write(a+'-- BEGIN %s\n'%mark+body+'\n-- END %s\n'%mark+c)
