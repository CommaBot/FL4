"""collapse A / B3 tidy-up after apply.py: drop prefixes left dangling by a deleted declaration
(`variable … in` / `set_option … in` directly before `end` or a blank line) and the sections the
deletion left holding only `variable`/`open` lines (only those not already empty on main)."""
import subprocess,re,sys
BASE=sys.argv[1] if len(sys.argv)>1 else 'c97a30ac1'
files=subprocess.check_output(['git','diff','--name-only','--diff-filter=M',BASE,'HEAD','--','proofs/Fl4Proofs']).decode().split()
PRE=re.compile(r'^((variable|set_option|open|include|omit)\b.*\bin|@\[[^\]]*\])\s*$')
def empties(L):
    out=[]
    for i,l in enumerate(L):
        if re.match(r'^(noncomputable )?section\b',l):
            j=i+1
            while j<len(L) and not re.match(r'^(end\b|section\b|noncomputable section|namespace)',L[j]): j+=1
            body=L[i+1:j]
            if j<len(L) and L[j].startswith('end') and all(b.strip()=='' or b.startswith('variable') or b.startswith('  ') or b.startswith('open ') for b in body):
                out.append((i,j))
    return out
tot_pre=tot_sec=0
for f in files:
    L=open(f).read().split('\n')
    M=subprocess.check_output(['git','show',f'{BASE}:{f}']).decode().split('\n')
    # 1. dangling prefixes
    keep=[]; i=0
    while i<len(L):
        if PRE.match(L[i]):
            j=i+1
            while j<len(L) and L[j].strip()=='': j+=1
            if j>i+1 or (j<len(L) and re.match(r'^(end\b|section\b|/-!)',L[j])):
                tot_pre+=1; print('PRE',f,i+1,L[i]); i+=1
                while i<len(L) and L[i].strip()=='' and keep and keep[-1].strip()=='': i+=1
                continue
        keep.append(L[i]); i+=1
    L=keep
    # 2. empty sections not empty on main
    mtxt={}
    for a,b in empties(M):
        t='\n'.join(M[a:b+1]); mtxt[t]=mtxt.get(t,0)+1
    drop=set()
    for a,b in empties(L):
        t='\n'.join(L[a:b+1])
        if mtxt.get(t,0)>0: mtxt[t]-=1; continue
        drop.update(range(a,b+1)); tot_sec+=1
        if b+1<len(L) and L[b+1].strip()=='': drop.add(b+1)
    L=[l for k,l in enumerate(L) if k not in drop]
    open(f,'w').write('\n'.join(L))
print('prefixes',tot_pre,'sections',tot_sec)
