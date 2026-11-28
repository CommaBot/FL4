"""jkren.py FILES... : code-only renames for collapse A, J (+K: pass --k)."""
import re,sys
def split(s):
    out=[];i=0;n=len(s);buf=[];code=True
    while i<n:
        if s.startswith('/-',i):
            out.append((True,''.join(buf)));buf=[]
            d=0;j=i
            while j<n:
                if s.startswith('/-',j): d+=1;j+=2;continue
                if s.startswith('-/',j):
                    d-=1;j+=2
                    if d==0: break
                    continue
                j+=1
            out.append((False,s[i:j]));i=j;continue
        if s.startswith('--',i):
            out.append((True,''.join(buf)));buf=[]
            j=s.find('\n',i); j=n if j<0 else j
            out.append((False,s[i:j]));i=j;continue
        if s[i]=='"':
            j=i+1
            while j<n and s[j]!='"':
                if s[j]=='\\': j+=1
                j+=1
            buf.append(s[i:j+1]);i=j+1;continue
        buf.append(s[i]);i+=1
    out.append((True,''.join(buf)))
    return out
K='--k' in sys.argv
W=[('JPathAtMU35','JPathAtMU30')]
P=[('Fl4ProofsKJ.','Fl4ProofsK.'),('Fl4ProofsJ.','Fl4Proofs.')]
if K:
    P=[('Fl4ProofsK.','Fl4Proofs.')]
    W=[('KFinAtRI','KFinAtR'),('KFinAtR27I','KFinAtR27'),('KFinAtR31I','KFinAtR31'),('KFinAtR5I','KFinAtR5'),
     ('to5I','to5'),('to31I','to31'),('to27I','to27'),('toRI','toR'),
     ('jat_scheduleWP0FZRI','jat_scheduleWP0FZR'),('jat_scheduleFR2ZRI','jat_scheduleFR2ZR'),('jat_scheduleSR2ZRPI','jat_scheduleSR2ZRP'),
     ('jat_finishJRPI','jat_finishJRP'),('jat_finishJRNI','jat_finishJRN'),('jat_finishJRNMQI','jat_finishJRNM'),
     ('jat_finishJRNMStQI','jat_finishJRNMSt'),('scnt_refines0FAI','scnt_refines0FA'),('sw_refinesFAI','sw_refinesFA'),
     ("ArchSwF'",'ArchSwF'),('msF_mrT','msF_mr')]
tot={}
for f in [a for a in sys.argv[1:] if a!='--k']:
    s=open(f).read(); parts=split(s); res=[]
    for code,t in parts:
        if code:
            for a,b in P:
                t,k=re.subn(r'(?<![\w])'+re.escape(a),b,t)
                if k: tot[(f,a)]=tot.get((f,a),0)+k
            for a,b in W:
                t,k=re.subn(r'(?<![\w])'+re.escape(a)+r'(?![\w\'])',b,t)
                if k: tot[(f,a)]=tot.get((f,a),0)+k
        res.append(t)
    r=''.join(res)
    if r!=s: open(f,'w').write(r)
for (f,a),k in sorted(tot.items()): print(f,a,k)
