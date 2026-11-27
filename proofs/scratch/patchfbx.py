# fb3c: IK-style generated families: X_fbEntryX + X_performFrameBatch (SpecFbX), before X_fl4ArchPerformInvocation
import re,sys
pat=re.compile(r'^theorem (\w+)_fl4ArchPerformInvocation \(a0 : Fl4ArchInvocation\) : (\w+)E( [^(]*?)? ?\(fl4ArchPerformInvocation \(Z := Unit\) a0\) := by\n  unfold fl4ArchPerformInvocation; (\w+)_auto\n', re.M)
for p in sys.argv[1:]:
    s=open(p).read()
    if 'performFrameBatch' in s: print('skip',p); continue
    m=pat.search(s)
    if not m: print('NOMATCH',p); continue
    pre,K,args,auto=m.group(1),m.group(2),(m.group(3) or '').strip(),m.group(4)
    a=(' '+args) if args else ''
    add=f'''/-- fb3c: one `X86PML4FrameBatch` entry, its frame `cap_delete` written out (SpecFbX). -/
theorem {pre}_fbEntryX (b : Fl4FrameBatchInvocation) (w : Data × Data × Data) : {K}E{a} (Fl4Proofs.P3.SInv.fbEntryX b w) := by
  unfold Fl4Proofs.P3.SInv.fbEntryX Fl4Proofs.P3.SInv.fbDeleteX Fl4Proofs.P3.SInv.fbDelX; {auto}_auto

/-- fb3c: the batch (`Fl4Proofs.P3.SInv.ik_performFrameBatchX`). -/
theorem {pre}_performFrameBatch (b : Fl4FrameBatchInvocation) : {K}{a} (performFrameBatch (Z := Unit) b) :=
  Fl4Proofs.P3.SInv.ik_performFrameBatchX (fun w => {pre}_fbEntryX b w) (by unfold flushAll; {auto}_auto)
macro_rules | `(tactic| {auto}_leaf) => `(tactic| with_reducible exact {pre}_performFrameBatch _)

'''
    s=s[:m.start()]+add+s[m.start():]
    imps=[l for l in s.split('\n') if l.startswith('import ')]
    last=imps[-1]
    s=s.replace(last+'\n', last+'\nimport Fl4Proofs.P3.SpecFbX\n',1)
    open(p,'w').write(s); print('patched',p,pre,K,a)
