"""collapse A / B3: map a dead decl set (recompute.py json) to source blocks (py/srcdecl.py).
usage: srcmap.py DEAD.json PROOFS_ROOT OUT.json   (PROOFS_ROOT = dir holding Fl4Proofs/)"""
import json,collections,sys,os
O,ROOT,OUT=sys.argv[1:4]
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'..','py','srcdecl.py')).read())
f=json.load(open(O)); D=set(f['D']); dmod=f['dmod']
bym=collections.defaultdict(set)
for x in D: bym[dmod[x]].add(x)
rows=[]; und=[]; mods={}; inblock=[]; auxblk=[]
import re
PFX_IN=re.compile(r'^(variable|open|omit|include|set_option)\b.*\bin\s*$')
AUXC=re.compile(r'^(match_\d+|proof_\d+|_proof_\d+|_simp_\d+|eq_\d+|eq_def|_unfold|_sunfold|_cstage\d*|_sparseCasesOn_\d+|splitter|congr_simp|inj|injEq|sizeOf_spec|noConfusion|noConfusionType|recOn|casesOn|below|brecOn|binductionOn|ibelow|_sizeOf_\d+|_sizeOf_inst|rec|_flat_ctor|refl|ctorIdx|_auxLemma\d*|_lambda_\d+|_override|elim|ctorElim|ctorElimType)$')
for m,xs in sorted(bym.items()):
    path=os.path.join(ROOT,m.replace('.','/')+'.lean')
    lines,bl=blocks(open(path).read())
    for b in bl:   # `variable … in` / `open … in` / `omit … in` / `include … in` prefixes belong to the block
        while b['start']>0 and PFX_IN.match(lines[b['start']-1]): b['start']-=1
    loc={b['name']:b for b in bl}
    # a block `X.refl` / `X.ext` / … (an AUXC suffix) is part of declaration X at the decl level (recompute.py's dmap)
    for b in bl:
        ps=b['name'].split('.')
        if b['name'] not in xs and len(ps)>2 and AUXC.match(ps[-1]) and '.'.join(ps[:-1]) in xs:
            xs.add(b['name']); auxblk.append((m,b['name']))
    dels=[loc[x] for x in xs if x in loc]
    for x in xs:
        if x in loc: continue
        p=x
        while '.' in p:
            p=p.rsplit('.',1)[0]
            if p in loc and p in xs: inblock.append((m,x)); break
        else: und.append((m,x))
    alive=[b for b in bl if b['name'] not in xs]
    mods[m]=dict(n=len(dels),nlines=sum(b['end']-b['start'] for b in dels),total=len(bl),alive=len(alive),flines=len(lines))
    for b in sorted(dels,key=lambda b:b['start']):
        rows.append((m,b['name'],b['kind'],b['start']+1,b['end']))
empty=sorted(m for m,v in mods.items() if v['alive']==0)
json.dump(dict(rows=rows,und=und,inblock=inblock,mods=mods,empty=empty,auxblk=auxblk),open(OUT,'w'))
print('aux-suffix blocks added',auxblk)
print('DEL decls',len(rows),'lines',sum(r[4]-r[3]+1 for r in rows),'modules',len(mods),'undeletable',len(und),'in-block',len(inblock))
print('emptied modules',len(empty),' '.join(e.replace('Fl4Proofs.','') for e in empty))
