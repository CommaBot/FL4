import re,sys,glob
fields=set("xtop call rfree rrecv yld mcp buf ks thT thk ip rp apart nk nodeB jpl cover obj zH sfree hset hscC jcov kern del ut bound finM utc nsc inv cur own off act c0 bsa sv isorted slink curRun blk intL vsc bok fcov fcap ext live zD carry".split())
SKIP=['JAtZR','JAtZS','JAtZB','JAtZV']
hdr=re.compile(r'^(?:private |protected )?(?:theorem|def|lemma|abbrev) ([A-Za-z0-9_\'.]+)',re.M)

def sigof(body):
    # mmu32: the signature ends at the first ':=' outside brackets (a '(L := L)' argument is not the end)
    d=0
    for i,ch in enumerate(body):
        if ch in '([{⦃': d+=1
        elif ch in ')]}⦄': d-=1
        elif ch==':' and d==0 and body[i+1:i+2]=='=': return body[:i]
    return body
defs={}
for f in sorted(glob.glob('Fl4Proofs/P3/*.lean')):
    if any(x in f for x in SKIP): continue
    txt=open(f).read()
    ms=list(hdr.finditer(txt))
    for i,m in enumerate(ms):
        end=ms[i+1].start() if i+1<len(ms) else len(txt)
        body=txt[m.start():end]
        # cut trailing doc/set_option/end lines belonging to next decl
        lines=body.split('\n')
        # find start of trailing junk: last line index of proof; drop trailing lines that are docstring start, set_option, end, section, namespace, variable, blank
        cut=len(lines)
        j=len(lines)-1
        # docstring of next decl begins with '/--' ; find last '/--' that starts a line after proof
        k=None
        for idx in range(1,len(lines)):
            if lines[idx].startswith('/--') or lines[idx].startswith('set_option') or re.match(r'^(end|section|namespace|variable|open|@\[|omit|include|/-)',lines[idx]):
                k=idx;break
        if k: lines=lines[:k]
        body='\n'.join(lines).rstrip()+'\n'
        # preceding docstring + set_option
        pre=txt[:m.start()]
        plines=pre.split('\n')[:-1]
        prefix=[]
        q=len(plines)-1
        # set_option lines directly above
        while q>=0 and plines[q].startswith('set_option'):
            prefix.insert(0,plines[q]); q-=1
        if q>=0 and plines[q].rstrip().endswith('-/'):
            r=q
            while r>=0 and not plines[r].startswith('/--'): r-=1
            if r>=0: prefix=plines[r:q+1]+prefix; q=r-1
            while q>=0 and plines[q].startswith('set_option'):
                prefix.insert(0,plines[q]); q-=1
        sig=sigof(body)
        if not re.search(r'\(J[0-9]*\s*:\s*JAtZ \(L',sig): continue
        name=m.group(1)
        short=name.split('.')[-1]
        key=short if (name.startswith('JAtZ.') or '.' not in name) else name
        if key in defs: print('DUP',key,f,defs[key][0],file=sys.stderr); continue
        defs[key]=(f,'\n'.join(prefix)+('\n' if prefix else '')+body,name)
roots=sys.argv[1:]
order=[];seen=set();ext=set()
def visit(n):
    if n in seen or n not in defs: return
    seen.add(n)
    f,b,_=defs[n]
    names=re.findall(r'\bJ[0-9]*\.([A-Za-z_][A-Za-z0-9_\']*)',b)
    if 'ext' in names: ext.add(n)
    for x in names:
        if x not in fields: visit(x)
    for k in defs:
        if '.' in k and k!=n and re.search(r'(?<![A-Za-z0-9_.])'+re.escape(k)+r'(?![A-Za-z0-9_\'])',b): visit(k)
    order.append(n)
for r in roots: visit(r)
out=[]
for n in order:
    f,b,name=defs[n]
    b=re.sub(r'\(J([0-9]*)\s*:\s*JAtZ \(L',r'(J\1 : JAtZB (L',b)
    if '.' in n:
        new=n+'B'
        b=b.replace('theorem '+name,'theorem '+new,1)
    else:
        b=re.sub(r'^((?:private |protected )?(?:theorem|def|lemma|abbrev) )'+re.escape(name)+r"(?![A-Za-z0-9_'])",lambda m:m.group(1)+'JAtZB.'+n,b,count=1,flags=re.M)
    for k in defs:
        if '.' in k:
            b=re.sub(r'(?<![A-Za-z0-9_.])'+re.escape(k)+r'(?![A-Za-z0-9_\'B])',k+'B',b)
    src=open(f).read()
    import re as _r
    mm=_r.search(r'namespace Fl4Proofs.P3\n(open [^\n]*)',src)
    op=mm.group(1) if mm else ''
    out.append('-- from '+f+(' (EXT)' if n in ext else '')+'\nsection\n'+op+'\n\n'+b.rstrip()+'\n\nend\n')
print('\n'.join(out))
print('ORDER',order,file=sys.stderr); print('EXT',ext,file=sys.stderr)
