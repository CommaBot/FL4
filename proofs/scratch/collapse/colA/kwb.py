"""collapse A, K: write P3KFin / ArchSwIdle's narrowed finish records back into the base declarations in place.
Run from proofs/. Swaps replace a base block (declaration line .. end, the base docstring / set_option kept) by
the `…I` block with the `…I` names renamed; moves carry the whole block (docstring / set_option included)."""
import re,sys
sys.path.insert(0,'scratch/collapse/colA'); from blk import block
exec(open('scratch/collapse/py/srcdecl.py').read())
D='Fl4Proofs/P3/'
REN=[('KFinAtRI','KFinAtR'),('KFinAtR27I','KFinAtR27'),('KFinAtR31I','KFinAtR31'),('KFinAtR5I','KFinAtR5'),
     ('to5I','to5'),('to31I','to31'),('to27I','to27'),('toRI','toR'),
     ('jat_scheduleWP0FZRI','jat_scheduleWP0FZR'),('jat_scheduleFR2ZRI','jat_scheduleFR2ZR'),('jat_scheduleSR2ZRPI','jat_scheduleSR2ZRP'),
     ('jat_finishJRPI','jat_finishJRP'),('jat_finishJRNI','jat_finishJRN'),('jat_finishJRNMQI','jat_finishJRNM'),
     ('jat_finishJRNMStQI','jat_finishJRNMSt'),('scnt_refines0FAI','scnt_refines0FA'),('sw_refinesFAI','sw_refinesFA'),
     ("ArchSwF'",'ArchSwF'),('msF_mrT','msF_mr')]
def ren(t):
    t=t.replace('Fl4ProofsK.','Fl4Proofs.')
    for a,b in REN: t=re.sub(r'(?<![\w])'+re.escape(a)+r'(?![\w\'])',b,t)
    return t
def full(path,name):
    lines,bl=blocks(open(path).read())
    bs=[b for b in bl if b['name']==name or b['name'].endswith('.'+name)]
    assert len(bs)==1,(path,name,len(bs))
    b=bs[0]; return lines[b['start']:b['end']]
def swap(dst,nd,src,ns):
    a=block(D+dst+'.lean',nd); s=block(D+src+'.lean',ns)
    assert a and s,(dst,nd,src,ns)
    L=open(D+dst+'.lean').read().split('\n')
    L[a[0]-1:a[1]]=ren('\n'.join(s[2])).split('\n')
    open(D+dst+'.lean','w').write('\n'.join(L)); print('SWAP',dst,nd,'<-',src,ns)
def insert_before(dst,nd,txt):
    """insert txt before the full block (docstring/set_option prefix included) of nd in dst"""
    lines,bl=blocks(open(D+dst+'.lean').read())
    bs=[b for b in bl if b['name'].endswith('.'+nd) or b['name']==nd]; assert len(bs)==1,(dst,nd)
    i=bs[0]['start']
    lines[i:i]=txt.split('\n')+['']
    open(D+dst+'.lean','w').write('\n'.join(lines)); print('INSERT',dst,'before',nd)
def delete(dst,names):
    lines,bl=blocks(open(D+dst+'.lean').read())
    PFX_IN=re.compile(r'^(variable|open|omit|include|set_option)\b.*\bin\s*$')
    rm=[]
    for n in names:
        bs=[b for b in bl if b['name']==n or b['name'].endswith('.'+n)]; assert len(bs)==1,(dst,n,len(bs))
        b=bs[0]
        while b['start']>0 and PFX_IN.match(lines[b['start']-1]): b['start']-=1
        rm.append(b)
    for b in sorted(rm,key=lambda b:-b['start']): del lines[b['start']:b['end']]; print('DEL',dst,b['name'])
    open(D+dst+'.lean','w').write('\n'.join(lines))
# 1. ScArchF: IdleVt (from G7eRoot), ArchSwFT / ArchSwFI (from ArchSwIdle) before ArchSwF; ArchSwF := ArchSwFT ∧ ArchSwFI
idle='\n'.join(full(D+'G7eRoot.lean','IdleVt'))
ft='\n'.join(full(D+'ArchSwIdle.lean','ArchSwFT')); fi='\n'.join(full(D+'ArchSwIdle.lean','ArchSwFI'))
nw="\n".join(full(D+'ArchSwIdle.lean',"ArchSwF'"))
p=D+'ScArchF.lean'; s=open(p).read()
k=s.index('namespace Fl4Proofs.P3.Sched\n')
s=s[:k]+'namespace Fl4Proofs.P3\n\n'+idle+'\n\nend Fl4Proofs.P3\n\n'+s[k:]
open(p,'w').write(s)
insert_before('ScArchF','ArchSwF',ft+'\n\n'+fi)
a=block(p,'ArchSwF'); L=open(p).read().split('\n')
body=nw.split('\n'); body=body[[i for i,l in enumerate(body) if l.startswith('def ')][0]:]
L[a[0]-1:a[1]]=ren('\n'.join(body)).split('\n'); open(p,'w').write('\n'.join(L)); print('ArchSwF body <- ArchSwF\'')
delete('G7eRoot',['IdleVt'])
# 2. G7eChain: the A-chain's two arch consumers
swap('G7eChain','scnt_refines0FA','ArchSwIdle','scnt_refines0FAI')
swap('G7eChain','sw_refinesFA','ArchSwIdle','sw_refinesFAI')
delete('ArchSwIdle',['ArchSwFT','ArchSwFI',"ArchSwF'",'ArchSwF.toN','scnt_refines0FAI','sw_refinesFAI'])
# 3. KEntry4: FinRootR / FinRootI + KFinAtR; the three scheduler lemmas move here from XTopJointJAtZRB (their only user
#    is jat_finishJRP), with P3KFin's bodies
fr='\n'.join(full(D+'P3KFin.lean','FinRootR')); fio='\n'.join(full(D+'P3KFin.lean','FinRootI'))
insert_before('XTopJointKEntry4','KFinAtR',fr+'\n\n'+fio)
swap('XTopJointKEntry4','KFinAtR','P3KFin','KFinAtRI')
sch='\n\n'.join(ren('\n'.join(full(D+'P3KFin.lean',n))) for n in ['jat_scheduleWP0FZRI','jat_scheduleFR2ZRI','jat_scheduleSR2ZRPI'])
insert_before('XTopJointKEntry4','jat_finishJRP',sch)
delete('XTopJointJAtZRB',['jat_scheduleWP0FZR','jat_scheduleFR2ZR','jat_scheduleSR2ZRP'])
swap('XTopJointKEntry4','jat_finishJRP','P3KFin','jat_finishJRPI')
# 4. the other records / conversions / finish lemmas in place
swap('XTopJointKEntryU5','KFinAtR5','P3KFin','KFinAtR5I')
swap('XTopJointKEntryU5','KFinAtR5.to31','P3KFin','KFinAtR5I.to31I')
swap('XTopJointKEntry31','KFinAtR31','P3KFin','KFinAtR31I')
swap('XTopJointKEntry31','KFinAtR31.to27','P3KFin','KFinAtR31I.to27I')
swap('XTopJointKEntry27','KFinAtR27','P3KFin','KFinAtR27I')
swap('XTopJointKEntry27','KFinAtR27.toR','P3KFin','KFinAtR27I.toRI')
swap('XTopJointKEntry28','jat_finishJRN','P3KFin','jat_finishJRNI')
swap('XTopJointKEntry36','jat_finishJRNM','P3KFin','jat_finishJRNMQI')
swap('StPostEv','jat_finishJRNMSt','P3JStIrqKFin','jat_finishJRNMStQI')
swap('G7eTail','KFinAtR8.to5','P3KFin','KFinAtR8.to5I')
p=D+'XTopJointKEntry4.lean'; s=open(p).read()
s=s.replace('import Fl4Proofs.P3.XTopJointJAtZRB\n','import Fl4Proofs.P3.XTopJointJAtZRB\nimport Fl4Proofs.P3.G7eChain\n',1); open(p,'w').write(s)
p=D+'G7eTail.lean'; s=open(p).read()
s=s.replace('(F : Fl4Proofs.P3.SInvR.G5.KFinAtR8 (L := L)','(F : KFinAtR8 (L := L)').replace('    Fl4Proofs.P3.SInvR.G5.kfin_tail_of J F.hd','    kfin_tail_of J F.hd')
open(p,'w').write(s)
