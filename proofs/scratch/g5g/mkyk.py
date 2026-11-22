# g5g: the YK family (memory half of untyped_ranges_zero) = sg1's SpecInvSgI1..I6 renamed,
# with new leaves (head1.lean) and without the functions reaching retype_region / fl4FpuToFrame.
import re
D='../../Fl4Proofs/P3/'
BAD=set('archPerformInvocation fl4ArchPerformInvocation fl4CallKernel fl4HandleEvent fl4HandleInvocationR fl4HandleSyscall fl4KernelEntrySyscall fl4PerformInvocation handleCall handleEvent handleInvocation handleSend invokeFl4Tcb invokeUntyped invokeUntypedWith performAsidControlInvocation performInvocation retypeRegion retypeRegionWith storeWordOffs portIn portOut'.split())
head=open('head1.lean').read()
for i in range(1,7):
    s=open(D+'SpecInvSgI%d.lean'%i).read()
    if i==1:
        k=s.index('theorem idk_archActivateIdleThread')
        body=s[k:].rsplit('\nend\n',1)[0]
    else:
        k=s.index('variable {N : ObjRef}\n')+len('variable {N : ObjRef}\n')
        body=s[k:].rsplit('\nend\n',1)[0]
    blocks=re.split(r'\n(?=theorem |set_option maxHeartbeats \d+ in\ntheorem |/--)',body)
    keep=[];drop=[]
    for b in blocks:
        m=re.search(r'theorem idk_(\w+)',b)
        if m and m.group(1) in BAD: drop.append(m.group(1)); continue
        keep.append(b)
    body='\n'.join(keep)
    body=re.sub(r'\bIdKE N\b','YKE PD FS',body); body=re.sub(r'\bIdK N\b','YK PD FS',body)
    body=body.replace('idk_','yk_')
    assert 'IdK' not in body and 'idk' not in body and 'IdleIs' not in body, i
    if i==1:
        out=head+'\nvariable {PD : PgSet} {FS : Set Nat}\n\n'+body+'\nend\n\nend Fl4Proofs.P3.SInvUZ\n'
    else:
        out='''/- g5g: the memory half `YK D F` of untyped_ranges_zero, part %d (sg1's SpecInvSgI%d renamed; see SpecInvUtZK1). -/
import Fl4Proofs.P3.SpecInvUtZK%d
open Classical

namespace Fl4Proofs.P3.SInvUZ
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {PD : PgSet} {FS : Set Nat}

'''%(i,i,i-1)+body+'\nend\n\nend Fl4Proofs.P3.SInvUZ\n'
    open(D+'SpecInvUtZK%d.lean'%i,'w').write(out)
    print(i,len(blocks),len(keep),drop)
