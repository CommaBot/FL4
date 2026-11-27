import json,re,sys,collections,os
exec(open('/private/tmp/claude-502/col/srcdecl.py').read())
exec(open('/private/tmp/claude-502/col/ana.py').read())
R='/Users/stillfail/.stillfail/sessions/claude-ember@d70ccd1321eaa3aa3390df77fb901ff2774a7cc3da926c3cf25ca287a3ba5f22/C0AQ0C0KVMH-1794890878-390829/workspace/FL4-collapse/proofs/'
dry='--apply' not in sys.argv
report=[]
for w,dump in [('x86','depdump.tsv.gz'),('a64','depdumpA64.tsv.gz')]:
    d=json.load(open(f'/private/tmp/claude-502/col/dead_{w}.json'))
    X=set(d['X'])
    mod,kind,deps=load(dump)
    bymod=collections.defaultdict(set)
    for c,m in mod.items(): bymod[m].add(c)
    for m in sorted(d['bym']):
        path=R+m.replace('.','/')+'.lean'
        text=open(path).read()
        lines,bl=blocks(text)
        consts=bymod[m]
        names=set()
        for b in bl:
            b['cn']=('_private.'+m+'.0.'+b['name']) if b['priv'] else b['name']
            names.add(b['cn'])
        dels=[]
        for b in bl:
            F=b['cn']
            gen={c for c in consts if c==F or (c.startswith(F+'.') and not any(c==o or c.startswith(o+'.') for o in names if o!=F and o.startswith(F+'.')))}
            if not gen: report.append(f'WARN no consts for {F} in {m}'); continue
            if gen<=X: dels.append(b)
        covered=set()
        for b in dels:
            F=b['cn']; covered|={c for c in X if mod.get(c)==m and (c==F or c.startswith(F+'.'))}
        miss=[c for c in d['bym'][m] if c not in covered and not re.search(r'(\.(match_\d+|proof_\d+|_proof_\d+|_simp_\d+|eq_\d+|eq_def|_unfold|_sunfold|_sparseCasesOn_\d+)$)',c)]
        for b in dels: report.append(f'DEL {w} {m} {b["name"]} ({b["kind"]}, lines {b["start"]+1}-{b["end"]})')
        for c in miss: report.append(f'KEEP-UNDELETABLE {w} {m} {c}')
        if not dels: continue
        drop=set()
        for b in dels: drop|=set(range(b['start'],b['end']))
        new=[l for i,l in enumerate(lines) if i not in drop]
        out='\n'.join(new)
        out=re.sub(r'\n{3,}','\n\n',out)
        if not dry: open(path,'w').write(out)
print('\n'.join(report))
