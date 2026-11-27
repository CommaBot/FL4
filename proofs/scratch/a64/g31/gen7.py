#!/usr/bin/env python3
# gen7.py: copy the KW-footprint cone (from the Lean cone dump) into namespace K7 with the TCB bound 224.
import re,sys
import os
P=os.path.join(os.path.dirname(os.path.abspath(__file__)),'../../../Fl4ProofsA64/P1/')
cone_file, runs_sel, out, modname, imports = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5]
L=[l.split() for l in open(cone_file) if l.startswith('CONE')]
runs=[];cur=None
STARTS=('Fl4ProofsA64.P1.fin_ntfn.blk','Fl4ProofsA64.P1.fin_reply.blk','Fl4ProofsA64.P1.fin_sc.blk','Fl4ProofsA64.P1.fin_thread.blk')
for x in L:
    if cur is None or x[4] in STARTS:
        cur={'names':set(),'items':[]}; runs.append(cur)
    cur['names'].add(x[4]); cur['items'].append(x)
sel=[int(i) for i in runs_sel.split(',')]
items={}
for i in sel:
    for x in runs[i]['items']:
        m=x[1].split('.')[-1]; a=int(x[2]); b=int(x[3]); n=x[4].replace('Fl4ProofsA64.P1.','',1)
        if a==0: continue
        items[(m,a)]=(m,a,b,n)
excl=set(sys.argv[6].split(',')) if len(sys.argv)>6 and sys.argv[6] else set()
order=['QueueFoot','QueueTimer','QueueTimerR','QueueFinal','QueueFinSc','QueueFootD','QueueReplyPop']
NONFAM=('LinkOf.','LawfulStore.NodeOf.','LawfulStore.QFoot.','EpFoot.','InRing.')
srcs={m:open(P+m+'.lean').read().split('\n') for m in order}
def newname(n):
    last=n.split('.')[-1]
    nn=n+'7' if last in ('kw','kwB') else n
    if nn!=n and n.startswith(NONFAM): return '_root_.Fl4ProofsA64.P1.'+nn
    return nn
meth=re.compile(r"(?<=[A-Za-z0-9_'!?.])\.(kw|kwB)(?![A-Za-z0-9_'!?])")
chunks=[]
cnt=0
for m in order:
    its=sorted([v for v in items.values() if v[0]==m], key=lambda v:v[1])
    if not its: continue
    lines=srcs[m]
    chunks.append(f'\n/-! ## From {m} -/\n')
    for (_,a,b,n) in its:
        if n in excl: continue
        s=a-1
        # extend upward: set_option ... in, attributes, docstring
        while s>0:
            p=lines[s-1]
            if re.match(r'^set_option .* in\s*$',p) or p.startswith('@['): s-=1; continue
            if p.rstrip().endswith('-/'):
                j=s-1
                while j>=0 and not lines[j].lstrip().startswith('/--') and not lines[j].lstrip().startswith('/-'): j-=1
                if j>=0 and lines[j].lstrip().startswith('/--'): s=j; continue
            break
        txt='\n'.join(lines[s:b])
        k=a-1
        while not re.match(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|abbrev|structure)\s',lines[k]): k+=1
        dl=lines[k]
        mm=re.match(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|abbrev|structure)\s+(\S+)',dl)
        assert mm, (m,a,dl)
        assert mm.group(2)==n, (m,a,mm.group(2),n)
        nn=newname(n)
        # rename the declared name
        txt=txt.replace(dl, dl.replace(mm.group(1)+' '+n, mm.group(1)+' '+'@@NAME@@',1),1)
        txt=meth.sub(lambda q:'.'+q.group(1)+'7',txt)
        txt=txt.replace('@@NAME@@',nn)
        txt=txt.replace('192','224')
        chunks.append(f'-- g31: copied from {m}:{a}-{b} (`{n}`), KW-family names over `K7` (TCB bound 224)\n'+txt+'\n')
        cnt+=1
DOC=open(os.path.join(os.path.dirname(os.path.abspath(__file__)),modname+'.doc')).read().rstrip('\n')
hdr=f'''/-
{DOC}
-/
{imports}
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {{S : Type _}} {{st : machine.Store S}} [L : LawfulStore st] {{T : Set U64}} {{Ω : Set U64}} {{H : Heap}}
variable {{Cs Sg Rp Scs Nt : Set U64}} {{Z : U64 → Nat}} {{Es : Set U64}}
variable {{X : Set U64}} {{Q : U64 → U64 → List U64}} {{R : U64 → List U64}}

namespace K7
'''
ftr='''
end K7

end

end Fl4ProofsA64.P1
'''
open(out,'w').write(hdr+'\n'.join(chunks)+ftr)
print('copied',cnt,'decls')
