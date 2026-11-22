# s26: the OB family (object half of valid_untyped for device caps) = SpecInvUtZK1..ZK6 (g5g's YK) renamed,
# with the new head headK1.lean. Run from proofs/scratch/s26.
import re
D='../../Fl4Proofs/P3/'
head=open('headK1.lean').read()
for i in range(1,7):
    s=open(D+'SpecInvUtZK%d.lean'%i).read()
    if i==1:
        k=s.index('theorem yk_archActivateIdleThread')
    else:
        k=s.index('variable {PD : PgSet} {FS : Set Nat}\n')+len('variable {PD : PgSet} {FS : Set Nat}\n')
    body=s[k:].rsplit('\nend\n',1)[0]
    body=re.sub(r'\bYKE PD FS\b','OBKE OS',body); body=re.sub(r'\bYK PD FS\b','OBK OS',body)
    body=body.replace('yk_','ob_')
    assert 'YK' not in body and 'yk' not in body and not re.search(r'\bPD\b|\bFS\b',body), (i, [l for l in body.split('\n') if 'YK' in l or 'yk' in l or 'PD' in l][:5])
    if i==1:
        out=head+'\nvariable {OS : ObSet}\n\n'+body+'\nend\n\nend Fl4Proofs.P3.SInvDV\n'
    else:
        out='''/- s26: the object half `OBK O` of device `valid_untyped`, part %d (SpecInvUtZK%d renamed; see SpecInvDvK1). -/
import Fl4Proofs.P3.SpecInvDvK%d
open Classical

namespace Fl4Proofs.P3.SInvDV
open Fl4Spec Fl4Proofs.P3.SInv

noncomputable section

set_option maxHeartbeats 1000000
set_option maxErrors 2000

variable {OS : ObSet}

'''%(i,i,i-1)+body+'\nend\n\nend Fl4Proofs.P3.SInvDV\n'
    open(D+'SpecInvDvK%d.lean'%i,'w').write(out)
    print(i,len(out.splitlines()))
