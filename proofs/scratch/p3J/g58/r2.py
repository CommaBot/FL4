import json,subprocess,re,sys,os
s=json.load(open(sys.argv[1]))
names=set()
for m,n,k,a,b in s['rows']:
    p=n.split('.'); names.add(p[-1]); 
    if len(p)>1: names.add('.'.join(p[-2:]))
mods={'P3JEptScope','P3JCapDomW'}
TOK=re.compile(r"[A-Za-z_][A-Za-z0-9_'.]*")
def scan(label,text):
    for i,l in enumerate(text.split('\n'),1):
        toks=set(TOK.findall(l)); last={x.split('.')[-1] for x in toks}|{'.'.join(x.split('.')[-2:]) for x in toks}
        d=sorted(x for x in names|mods if x in last)
        if d: print(f'HIT {label}:{i}: {d} | {l.strip()[:140]}')
mode=sys.argv[2]
if mode=='branch':
    b,lst=sys.argv[3],sys.argv[4]
    for f in open(lst).read().split():
        try: t=subprocess.check_output(['git','show',f'{b}:{f}'],text=True,stderr=subprocess.DEVNULL)
        except Exception: continue
        scan(b+':'+f,t)
else:
    root,lst=sys.argv[3],sys.argv[4]
    for f in open(lst).read().split():
        p=os.path.join(root,f)
        if os.path.isfile(p): scan('wt:'+f,open(p,errors='replace').read())
