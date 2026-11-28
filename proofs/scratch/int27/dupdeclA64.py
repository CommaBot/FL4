# repo-wide duplicate fully-qualified declaration check over root-reachable modules
import re,os,sys,collections
root='proofs'
imps=[l.split()[1] for l in open(root+'/Fl4ProofsA64.lean') if l.startswith('import ')]
# closure over Fl4Proofs.* modules
seen=set(); st=list(imps)
while st:
    m=st.pop()
    if m in seen or not m.startswith(('Fl4Proofs','Fl4Core','Fl4Spec','Fl4ProofsA64','Fl4CoreA64')): continue
    p=root+'/'+m.replace('.','/')+'.lean'
    if not os.path.exists(p): continue
    seen.add(m)
    for l in open(p,errors='replace'):
        if l.startswith('import '): st.append(l.split()[1])
KW=r'(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)'
dre=re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:(private|protected|noncomputable|partial|unsafe|nonrec)\s+)*'+KW+r'\s+([^\s:({\[⦃]+)')
defs=collections.defaultdict(set)
for m in seen:
    p=root+'/'+m.replace('.','/')+'.lean'
    ns=[]; inc=0
    txt=open(p,errors='replace').read()
    txt=re.sub(r'/-.*?-/','',txt,flags=re.S)
    for l in txt.splitlines():
        s=l.strip()
        mm=re.match(r'namespace\s+(\S+)',s)
        if mm: ns.append(('n',mm.group(1))); continue
        mm=re.match(r'section\b\s*(\S*)',s)
        if mm and not s.startswith('sectionX'): ns.append(('s',mm.group(1))); continue
        mm=re.match(r'end\b\s*(\S*)',s)
        if mm and ns and l.startswith('end'): ns.pop(); continue
        mm=dre.match(l)
        if mm and not l.startswith((' ','\t')):
            if 'private' in (l.split(KW)[0] if False else l[:mm.start(2)]): continue
            if re.search(r'\binstance\b',l[:mm.start(2)]) : continue
            n=mm.group(2)
            if n.startswith('_root_.'): fq=n[7:]
            else: fq='.'.join([x for k,x in ns if k=='n']+[n])
            defs[fq].add(p)
bad={k:v for k,v in defs.items() if len(v)>1}
print('modules',len(seen),'decls',len(defs),'dups',len(bad))
for k,v in sorted(bad.items()): print(k, sorted(v))
