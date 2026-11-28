"""collapse A, J: write P3JLook's narrowed path premises back into the base definitions in place.
Run from proofs/. Each base def / conversion / consumer block is replaced by its P3JLook `…L` block with the
`…L` names renamed to the base ones (`JPathAtMU35` ↦ `JPathAtMU30`)."""
import re,sys
sys.path.insert(0,'scratch/collapse/colA'); from blk import block
D='Fl4Proofs/P3/'
LK=D+'P3JLook.lean'
U=[4,7,12,17,18,19,21,25,26,27,28,29]
REN=[('JPathAtML','JPathAtM'),('JPathAtM35L','JPathAtM35'),('JPathAtM35EL','JPathAtM35E'),('JPathAtM36EL','JPathAtM36E'),
     ('JPathAtMU35','JPathAtMU30'),('toML','toM'),('to35L','to35'),('to35EL','to35E'),('to36EL','to36E'),
     ('handle_invocation_entryJMUL','handle_invocation_entryJMU'),('handle_invocation_entryJMUML','handle_invocation_entryJMUM')]
REN+=[('JPathAtMU%dL'%i,'JPathAtMU%d'%i) for i in U]+[('toU%dL'%i,'toU%d'%i) for i in U]
def ren(t):
    for a,b in REN: t=re.sub(r'(?<![\w])'+re.escape(a)+r'(?![\w\'])',b,t)
    return t
# (base file, base name, P3JLook name)
F={'JPathAtM':'XTopJointKEntry23P','JPathAtM35':'XTopJointKEntry35','JPathAtM35E':'XTopJointKEntry35E','JPathAtM36E':'XTopJointKEntry36E'}
for i in U: F['JPathAtMU%d'%i]='XTopJointKEntryU%d'%i
F['JPathAtMU30']='XTopJointKEntryU30'
pairs=[]
for b,f in F.items():
    l='JPathAtMU35' if b=='JPathAtMU30' else b+'L'
    pairs.append((f,b,l))
conv=[('XTopJointKEntry35','JPathAtM35.toM','JPathAtM35L.toML'),('XTopJointKEntry35E','JPathAtM35E.to35','JPathAtM35EL.to35L'),
      ('XTopJointKEntry36E','JPathAtM36E.to35E','JPathAtM36EL.to35EL'),('XTopJointKEntryU4','JPathAtMU4.to36E','JPathAtMU4L.to36EL')]
chain=[(7,4),(12,7),(17,12),(18,17),(19,18),(21,19),(25,21),(26,25),(27,26),(28,27),(29,28)]
conv+=[('XTopJointKEntryU%d'%a,'JPathAtMU%d.toU%d'%(a,b),'JPathAtMU%dL.toU%dL'%(a,b)) for a,b in chain]
conv+=[('XTopJointKEntryU30','JPathAtMU30.toU29','JPathAtMU35.toU29L'),
       ('XTopJointKEntry23P','handle_invocation_entryJMU','handle_invocation_entryJMUL'),
       ('XTopJointKEntry38','handle_invocation_entryJMUM','handle_invocation_entryJMUML')]
for f,b,l in pairs+conv:
    p=D+f+'.lean'
    a=block(p,b); s=block(LK,l)
    assert a and s,(f,b,l,bool(a),bool(s))
    txt=ren('\n'.join(s[2]))
    L=open(p).read().split('\n')
    old='\n'.join(L[a[0]-1:a[1]])
    L[a[0]-1:a[1]]=txt.split('\n')
    open(p,'w').write('\n'.join(L))
    print('SWAP',f,b,'<-',l,a[0],a[1],'lines',a[1]-a[0]+1,'->',len(s[2]))
